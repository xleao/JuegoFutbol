const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: '*' }
});

app.use(express.static(path.join(__dirname, 'public')));

// ─── CONSTANTS ───────────────────────────────────────────────
const TICK_RATE = 60;
const SEND_RATE = 20; // Network sends per second (client interpolates)
const SEND_EVERY = Math.round(TICK_RATE / SEND_RATE); // Send every N ticks
const FIELD_W = 1200;
const FIELD_H = 600;
const WALL_THICKNESS = 6;
const GOAL_SIZE = 160;
const PLAYER_RADIUS = 18;
const BALL_RADIUS = 12;
const PLAYER_SPEED = 0.35;
const PLAYER_KICK_POWER = 3.5;
const KICK_RANGE = PLAYER_RADIUS + BALL_RADIUS + 6;
const FRICTION_PLAYER = 0.94;
const FRICTION_BALL = 0.985;
const BOUNCE_FACTOR = 0.6;
const MAX_SCORE = 5;
const KICKOFF_FREEZE_MS = 1500;

// ─── ROOMS ───────────────────────────────────────────────────
const rooms = new Map();

function createBall() {
  return {
    x: FIELD_W / 2,
    y: FIELD_H / 2,
    vx: 0,
    vy: 0,
    radius: BALL_RADIUS
  };
}

function createRoom(id, name, password, maxPlayers, hostId) {
  return {
    id,
    name,
    password: password || null,
    maxPlayers: maxPlayers || 10,
    hostId,
    players: new Map(),
    ball: createBall(),
    scoreRed: 0,
    scoreBlue: 0,
    gameRunning: false,
    kickoffFreezeUntil: 0,
    lastGoalTeam: null,
    chatHistory: [],
    gameInterval: null,
    maxScore: MAX_SCORE,
    timeLimit: 180, // 3 minutes
    gameTimer: 0,
    gameStartedAt: null,
  };
}

function addPlayerToRoom(room, socketId, nickname) {
  // Auto-assign team: balance teams
  const reds = [...room.players.values()].filter(p => p.team === 'red').length;
  const blues = [...room.players.values()].filter(p => p.team === 'blue').length;
  let team = 'spectator';
  if (reds <= blues) team = 'red';
  else team = 'blue';

  const player = {
    id: socketId,
    nickname,
    team,
    x: 0,
    y: 0,
    vx: 0,
    vy: 0,
    radius: PLAYER_RADIUS,
    input: { up: false, down: false, left: false, right: false, kick: false },
    goals: 0,
    assists: 0,
    ping: 0,
    lastProcessedSeq: 0,
  };

  spawnPlayer(player, room);
  room.players.set(socketId, player);
  return player;
}

function spawnPlayer(player, room) {
  const teamPlayers = [...room.players.values()].filter(p => p.team === player.team);
  const index = teamPlayers.length;

  if (player.team === 'red') {
    player.x = 200;
    player.y = FIELD_H / 2 - 80 + index * 80;
  } else if (player.team === 'blue') {
    player.x = FIELD_W - 200;
    player.y = FIELD_H / 2 - 80 + index * 80;
  } else {
    player.x = -100;
    player.y = -100;
  }
  player.vx = 0;
  player.vy = 0;
}

function spawnAllPlayers(room) {
  let redIdx = 0, blueIdx = 0;
  room.players.forEach(p => {
    if (p.team === 'red') {
      p.x = 150 + (redIdx % 2) * 100;
      p.y = FIELD_H / 2 - 100 + Math.floor(redIdx / 2) * 100 + (redIdx % 2) * 50;
      if (p.y < 60) p.y = 60;
      if (p.y > FIELD_H - 60) p.y = FIELD_H - 60;
      redIdx++;
    } else if (p.team === 'blue') {
      p.x = FIELD_W - 150 - (blueIdx % 2) * 100;
      p.y = FIELD_H / 2 - 100 + Math.floor(blueIdx / 2) * 100 + (blueIdx % 2) * 50;
      if (p.y < 60) p.y = 60;
      if (p.y > FIELD_H - 60) p.y = FIELD_H - 60;
      blueIdx++;
    }
    p.vx = 0;
    p.vy = 0;
  });
}

function resetField(room) {
  room.ball = createBall();
  spawnAllPlayers(room);
  room.kickoffFreezeUntil = Date.now() + KICKOFF_FREEZE_MS;
}

// ─── PHYSICS ─────────────────────────────────────────────────
function circleDist(a, b) {
  const dx = a.x - b.x;
  const dy = a.y - b.y;
  return Math.sqrt(dx * dx + dy * dy);
}

function resolveCircleCollisionWithMass(a, b, massA, massB, bounce) {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  const dist = Math.sqrt(dx * dx + dy * dy);
  const minDist = a.radius + b.radius;

  if (dist < minDist && dist > 0) {
    const nx = dx / dist;
    const ny = dy / dist;
    const overlap = minDist - dist;

    const totalMass = massA + massB;
    const ratioA = massB / totalMass;
    const ratioB = massA / totalMass;

    // Separate
    a.x -= nx * overlap * ratioA;
    a.y -= ny * overlap * ratioA;
    b.x += nx * overlap * ratioB;
    b.y += ny * overlap * ratioB;

    // Relative velocity
    const dvx = a.vx - b.vx;
    const dvy = a.vy - b.vy;
    const dvn = dvx * nx + dvy * ny;

    if (dvn > 0) {
      const impulse = (1 + bounce) * dvn / (1 / massA + 1 / massB);
      a.vx -= (impulse / massA) * nx;
      a.vy -= (impulse / massA) * ny;
      b.vx += (impulse / massB) * nx;
      b.vy += (impulse / massB) * ny;
    }
  }
}

function resolveBallWallAndPostCollisions(ball) {
  const goalTop = FIELD_H / 2 - GOAL_SIZE / 2;
  const goalBottom = FIELD_H / 2 + GOAL_SIZE / 2;

  // Top wall
  if (ball.y - ball.radius < WALL_THICKNESS) {
    ball.y = WALL_THICKNESS + ball.radius;
    ball.vy *= -BOUNCE_FACTOR;
  }
  // Bottom wall
  if (ball.y + ball.radius > FIELD_H - WALL_THICKNESS) {
    ball.y = FIELD_H - WALL_THICKNESS - ball.radius;
    ball.vy *= -BOUNCE_FACTOR;
  }

  // Left wall (with goal gap)
  if (ball.x - ball.radius < WALL_THICKNESS) {
    if (ball.y < goalTop || ball.y > goalBottom) {
      ball.x = WALL_THICKNESS + ball.radius;
      ball.vx *= -BOUNCE_FACTOR;
    }
  }
  // Right wall (with goal gap)
  if (ball.x + ball.radius > FIELD_W - WALL_THICKNESS) {
    if (ball.y < goalTop || ball.y > goalBottom) {
      ball.x = FIELD_W - WALL_THICKNESS - ball.radius;
      ball.vx *= -BOUNCE_FACTOR;
    }
  }

  // Goal posts (circles at corners of goal)
  const posts = [
    { x: WALL_THICKNESS, y: goalTop, radius: 6 },
    { x: WALL_THICKNESS, y: goalBottom, radius: 6 },
    { x: FIELD_W - WALL_THICKNESS, y: goalTop, radius: 6 },
    { x: FIELD_W - WALL_THICKNESS, y: goalBottom, radius: 6 },
  ];
  posts.forEach(post => {
    const dx = ball.x - post.x;
    const dy = ball.y - post.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    const minDist = ball.radius + post.radius;
    if (dist < minDist && dist > 0) {
      const nx = dx / dist;
      const ny = dy / dist;
      ball.x = post.x + nx * minDist;
      ball.y = post.y + ny * minDist;
      const dot = ball.vx * nx + ball.vy * ny;
      ball.vx -= 2 * dot * nx * BOUNCE_FACTOR;
      ball.vy -= 2 * dot * ny * BOUNCE_FACTOR;
    }
  });

  // Goal back walls (prevent ball from going too far)
  const GOAL_DEPTH = 40;
  // Left goal area
  if (ball.x < -GOAL_DEPTH) {
    ball.x = -GOAL_DEPTH;
    ball.vx *= -0.3;
  }
  // Right goal area
  if (ball.x > FIELD_W + GOAL_DEPTH) {
    ball.x = FIELD_W + GOAL_DEPTH;
    ball.vx *= -0.3;
  }
}

function updatePhysics(room) {
  const now = Date.now();
  const frozen = now < room.kickoffFreezeUntil;

  // Update game timer
  if (room.gameStartedAt) {
    room.gameTimer = Math.floor((now - room.gameStartedAt) / 1000);
  }

  // Check time limit
  if (room.timeLimit > 0 && room.gameTimer >= room.timeLimit) {
    endGame(room, room.scoreRed > room.scoreBlue ? 'red' : (room.scoreBlue > room.scoreRed ? 'blue' : 'draw'));
    return;
  }

  // 1. Process player inputs and update positions
  room.players.forEach(player => {
    if (player.team === 'spectator') return;

    let ax = 0, ay = 0;
    if (player.input.up) ay -= PLAYER_SPEED;
    if (player.input.down) ay += PLAYER_SPEED;
    if (player.input.left) ax -= PLAYER_SPEED;
    if (player.input.right) ax += PLAYER_SPEED;

    // Normalize diagonal
    if (ax !== 0 && ay !== 0) {
      ax *= 0.707;
      ay *= 0.707;
    }

    player.vx += ax;
    player.vy += ay;
    player.vx *= FRICTION_PLAYER;
    player.vy *= FRICTION_PLAYER;

    if (!frozen) {
      player.x += player.vx;
      player.y += player.vy;
    }

    // Initial clamp to field
    player.x = Math.max(player.radius + WALL_THICKNESS, Math.min(FIELD_W - player.radius - WALL_THICKNESS, player.x));
    player.y = Math.max(player.radius + WALL_THICKNESS, Math.min(FIELD_H - player.radius - WALL_THICKNESS, player.y));
  });

  if (frozen) return;

  // 2. Ball physics (friction and position update)
  room.ball.vx *= FRICTION_BALL;
  room.ball.vy *= FRICTION_BALL;
  room.ball.x += room.ball.vx;
  room.ball.y += room.ball.vy;

  // 3. Process player kick inputs with velocity redirection
  room.players.forEach(player => {
    if (player.team === 'spectator') return;
    if (player.input.kick) {
      const dist = circleDist(player, room.ball);
      if (dist < KICK_RANGE) {
        const dx = room.ball.x - player.x;
        const dy = room.ball.y - player.y;
        const d = Math.sqrt(dx * dx + dy * dy) || 1;
        
        const kickDirX = dx / d;
        const kickDirY = dy / d;
        
        // Redirect existing ball velocity: project onto kick direction
        const speedProj = room.ball.vx * kickDirX + room.ball.vy * kickDirY;
        if (speedProj < 0) {
          // Cancel out incoming velocity component in the kick direction
          room.ball.vx -= speedProj * kickDirX;
          room.ball.vy -= speedProj * kickDirY;
        }
        
        room.ball.vx += kickDirX * PLAYER_KICK_POWER;
        room.ball.vy += kickDirY * PLAYER_KICK_POWER;
        room.ball.lastTouchedBy = player.id;
      }
    }
  });

  // 4. Authoritative Multi-Pass Physics Solver (3 iterations)
  for (let iter = 0; iter < 3; iter++) {
    // A. Player-Player collisions
    const playersArr = [...room.players.values()].filter(p => p.team !== 'spectator');
    for (let i = 0; i < playersArr.length; i++) {
      for (let j = i + 1; j < playersArr.length; j++) {
        resolveCircleCollisionWithMass(playersArr[i], playersArr[j], 1, 1, 0.5);
      }
    }

    // B. Player-Ball collisions
    room.players.forEach(player => {
      if (player.team === 'spectator') return;
      const dist = circleDist(player, room.ball);
      const minDist = player.radius + room.ball.radius;
      if (dist < minDist && dist > 0) {
        resolveCircleCollisionWithMass(player, room.ball, 2.5, 0.5, 0.45);
        room.ball.lastTouchedBy = player.id;
      }
    });

    // C. Clamp players to field boundaries
    room.players.forEach(player => {
      if (player.team === 'spectator') return;
      player.x = Math.max(player.radius + WALL_THICKNESS, Math.min(FIELD_W - player.radius - WALL_THICKNESS, player.x));
      player.y = Math.max(player.radius + WALL_THICKNESS, Math.min(FIELD_H - player.radius - WALL_THICKNESS, player.y));
    });

    // D. Resolve ball-wall and post collisions
    resolveBallWallAndPostCollisions(room.ball);
  }

  // 5. Goal detection (runs after authoritative physics are settled)
  const goalTop = FIELD_H / 2 - GOAL_SIZE / 2;
  const goalBottom = FIELD_H / 2 + GOAL_SIZE / 2;

  if (room.ball.x < 0 && room.ball.y > goalTop && room.ball.y < goalBottom) {
    // GOAL for Blue team!
    room.scoreBlue++;
    const scorer = room.players.get(room.ball.lastTouchedBy);
    if (scorer) scorer.goals++;
    broadcastToRoom(room, 'goalScored', {
      team: 'blue',
      scorer: scorer ? scorer.nickname : 'Unknown',
      scoreRed: room.scoreRed,
      scoreBlue: room.scoreBlue
    });
    if (room.scoreBlue >= room.maxScore) {
      endGame(room, 'blue');
    } else {
      resetField(room);
    }
    return;
  }
  if (room.ball.x > FIELD_W && room.ball.y > goalTop && room.ball.y < goalBottom) {
    // GOAL for Red team!
    room.scoreRed++;
    const scorer = room.players.get(room.ball.lastTouchedBy);
    if (scorer) scorer.goals++;
    broadcastToRoom(room, 'goalScored', {
      team: 'red',
      scorer: scorer ? scorer.nickname : 'Unknown',
      scoreRed: room.scoreRed,
      scoreBlue: room.scoreBlue
    });
    if (room.scoreRed >= room.maxScore) {
      endGame(room, 'red');
    } else {
      resetField(room);
    }
    return;
  }
}

function endGame(room, winner) {
  room.gameRunning = false;
  if (room.gameInterval) {
    clearInterval(room.gameInterval);
    room.gameInterval = null;
  }
  room.gameStartedAt = null;
  broadcastToRoom(room, 'gameEnded', {
    winner,
    scoreRed: room.scoreRed,
    scoreBlue: room.scoreBlue
  });
}

function startGame(room) {
  if (room.gameRunning) return;

  const reds = [...room.players.values()].filter(p => p.team === 'red').length;
  const blues = [...room.players.values()].filter(p => p.team === 'blue').length;
  if (reds < 1 || blues < 1) return;

  room.scoreRed = 0;
  room.scoreBlue = 0;
  room.gameRunning = true;
  room.gameTimer = 0;
  room.gameStartedAt = Date.now();
  room.tickCount = 0;
  resetField(room);

  broadcastToRoom(room, 'gameStarted', {});

  room.gameInterval = setInterval(() => {
    if (!room.gameRunning) {
      clearInterval(room.gameInterval);
      room.gameInterval = null;
      return;
    }
    updatePhysics(room);
    room.tickCount++;
    // Only send state at SEND_RATE Hz, not every physics tick
    if (room.tickCount % SEND_EVERY === 0) {
      broadcastGameState(room);
    }
  }, 1000 / TICK_RATE);
}

function broadcastGameState(room) {
  const players = [];
  room.players.forEach(p => {
    players.push({
      id: p.id,
      team: p.team,
      x: Math.round(p.x * 10) / 10,
      y: Math.round(p.y * 10) / 10,
      vx: Math.round(p.vx * 100) / 100,
      vy: Math.round(p.vy * 100) / 100,
      radius: p.radius,
      goals: p.goals,
      ping: p.ping || 0,
      lastProcessedSeq: p.lastProcessedSeq || 0,
    });
  });

  const state = {
    players,
    ball: {
      x: Math.round(room.ball.x * 10) / 10,
      y: Math.round(room.ball.y * 10) / 10,
      vx: Math.round(room.ball.vx * 100) / 100,
      vy: Math.round(room.ball.vy * 100) / 100,
      radius: room.ball.radius,
    },
    scoreRed: room.scoreRed,
    scoreBlue: room.scoreBlue,
    gameTimer: room.gameTimer,
    timeLimit: room.timeLimit,
    frozen: Date.now() < room.kickoffFreezeUntil,
    serverTime: Date.now(),
  };

  io.to(room.id).emit('gameState', state);
}

function broadcastToRoom(room, event, data) {
  io.to(room.id).emit(event, data);
}

function getRoomList() {
  const list = [];
  rooms.forEach(room => {
    list.push({
      id: room.id,
      name: room.name,
      hasPassword: !!room.password,
      playerCount: room.players.size,
      maxPlayers: room.maxPlayers,
      gameRunning: room.gameRunning,
      scoreRed: room.scoreRed,
      scoreBlue: room.scoreBlue,
    });
  });
  return list;
}

function getPlayersInRoom(room) {
  const players = [];
  room.players.forEach(p => {
    players.push({
      id: p.id,
      nickname: p.nickname,
      team: p.team,
      goals: p.goals,
      isHost: p.id === room.hostId,
    });
  });
  return players;
}

// ─── SOCKET EVENTS ───────────────────────────────────────────
io.on('connection', (socket) => {
  let currentRoom = null;
  let nickname = 'Player';

  socket.on('setNickname', (name) => {
    nickname = (name || 'Player').substring(0, 16);
  });

  socket.on('getRooms', () => {
    socket.emit('roomList', getRoomList());
  });

  socket.on('pingRequest', (data) => {
    socket.emit('pingResponse', data);
  });

  socket.on('pingUpdate', (pingVal) => {
    if (currentRoom) {
      const player = currentRoom.players.get(socket.id);
      if (player) {
        player.ping = pingVal;
      }
    }
  });

  socket.on('createRoom', (data) => {
    const roomId = 'room_' + Date.now() + '_' + Math.random().toString(36).substr(2, 4);
    const room = createRoom(
      roomId,
      (data.name || 'Sala sin nombre').substring(0, 30),
      data.password || null,
      Math.min(Math.max(data.maxPlayers || 10, 2), 20),
      socket.id
    );
    rooms.set(roomId, room);

    // Join the room
    socket.join(roomId);
    currentRoom = room;
    const player = addPlayerToRoom(room, socket.id, nickname);

    socket.emit('roomJoined', {
      roomId: room.id,
      roomName: room.name,
      isHost: true,
      player,
      players: getPlayersInRoom(room),
      maxScore: room.maxScore,
      timeLimit: room.timeLimit,
    });

    io.emit('roomList', getRoomList());
  });

  socket.on('joinRoom', (data) => {
    const room = rooms.get(data.roomId);
    if (!room) {
      socket.emit('joinError', 'La sala no existe.');
      return;
    }
    if (room.players.size >= room.maxPlayers) {
      socket.emit('joinError', 'La sala está llena.');
      return;
    }
    if (room.password && data.password !== room.password) {
      socket.emit('joinError', 'Contraseña incorrecta.');
      return;
    }

    socket.join(room.id);
    currentRoom = room;
    const player = addPlayerToRoom(room, socket.id, nickname);

    socket.emit('roomJoined', {
      roomId: room.id,
      roomName: room.name,
      isHost: socket.id === room.hostId,
      player,
      players: getPlayersInRoom(room),
      maxScore: room.maxScore,
      timeLimit: room.timeLimit,
    });

    broadcastToRoom(room, 'playerJoined', {
      player: { id: player.id, nickname: player.nickname, team: player.team },
      players: getPlayersInRoom(room),
    });

    io.emit('roomList', getRoomList());

    // System message
    broadcastToRoom(room, 'chatMessage', {
      type: 'system',
      message: `${nickname} se unió a la sala.`
    });
  });

  socket.on('leaveRoom', () => {
    if (!currentRoom) return;
    leaveCurrentRoom(socket);
  });

  socket.on('changeTeam', (team) => {
    if (!currentRoom) return;
    const player = currentRoom.players.get(socket.id);
    if (!player) return;
    if (!['red', 'blue', 'spectator'].includes(team)) return;
    if (currentRoom.gameRunning) return;

    player.team = team;
    spawnPlayer(player, currentRoom);

    broadcastToRoom(currentRoom, 'playerChangedTeam', {
      playerId: socket.id,
      team,
      players: getPlayersInRoom(currentRoom),
    });
  });

  socket.on('startGame', () => {
    if (!currentRoom) return;
    if (socket.id !== currentRoom.hostId) return;
    startGame(currentRoom);
  });

  socket.on('stopGame', () => {
    if (!currentRoom) return;
    if (socket.id !== currentRoom.hostId) return;
    endGame(currentRoom, 'stopped');
  });

  socket.on('updateSettings', (data) => {
    if (!currentRoom) return;
    if (socket.id !== currentRoom.hostId) return;
    if (currentRoom.gameRunning) return;

    if (data.maxScore) currentRoom.maxScore = Math.min(Math.max(data.maxScore, 1), 20);
    if (data.timeLimit !== undefined) currentRoom.timeLimit = Math.min(Math.max(data.timeLimit, 0), 600);

    broadcastToRoom(currentRoom, 'settingsUpdated', {
      maxScore: currentRoom.maxScore,
      timeLimit: currentRoom.timeLimit,
    });
  });

  socket.on('kickPlayer', (playerId) => {
    if (!currentRoom) return;
    if (socket.id !== currentRoom.hostId) return;
    if (playerId === socket.id) return;

    const targetSocket = io.sockets.sockets.get(playerId);
    if (targetSocket) {
      targetSocket.emit('kicked', 'Has sido expulsado de la sala.');
      const player = currentRoom.players.get(playerId);
      if (player) {
        broadcastToRoom(currentRoom, 'chatMessage', {
          type: 'system',
          message: `${player.nickname} fue expulsado.`
        });
      }
      currentRoom.players.delete(playerId);
      targetSocket.leave(currentRoom.id);
      broadcastToRoom(currentRoom, 'playerLeft', {
        playerId,
        players: getPlayersInRoom(currentRoom),
      });
      io.emit('roomList', getRoomList());
    }
  });

  socket.on('playerInput', (data) => {
    if (!currentRoom) return;
    const player = currentRoom.players.get(socket.id);
    if (!player) return;
    if (data && typeof data.seq === 'number') {
      if (data.seq > player.lastProcessedSeq) {
        player.input = {
          up: !!data.keys?.up,
          down: !!data.keys?.down,
          left: !!data.keys?.left,
          right: !!data.keys?.right,
          kick: !!data.keys?.kick,
        };
        player.lastProcessedSeq = data.seq;
      }
    } else if (data) {
      player.input = {
        up: !!data.up,
        down: !!data.down,
        left: !!data.left,
        right: !!data.right,
        kick: !!data.kick,
      };
    }
  });

  socket.on('chatMessage', (msg) => {
    if (!currentRoom) return;
    const text = (msg || '').substring(0, 200).trim();
    if (!text) return;

    const chatMsg = {
      type: 'player',
      nickname,
      team: currentRoom.players.get(socket.id)?.team || 'spectator',
      message: text,
    };
    currentRoom.chatHistory.push(chatMsg);
    if (currentRoom.chatHistory.length > 100) currentRoom.chatHistory.shift();

    broadcastToRoom(currentRoom, 'chatMessage', chatMsg);
  });

  socket.on('disconnect', () => {
    if (currentRoom) {
      leaveCurrentRoom(socket);
    }
  });

  function leaveCurrentRoom(sock) {
    if (!currentRoom) return;
    const player = currentRoom.players.get(sock.id);
    const playerName = player ? player.nickname : 'Unknown';
    currentRoom.players.delete(sock.id);
    sock.leave(currentRoom.id);

    broadcastToRoom(currentRoom, 'chatMessage', {
      type: 'system',
      message: `${playerName} abandonó la sala.`
    });

    // Transfer host
    if (currentRoom.hostId === sock.id && currentRoom.players.size > 0) {
      const newHost = currentRoom.players.keys().next().value;
      currentRoom.hostId = newHost;
      const newHostPlayer = currentRoom.players.get(newHost);
      broadcastToRoom(currentRoom, 'chatMessage', {
        type: 'system',
        message: `${newHostPlayer.nickname} es el nuevo host.`
      });
    }

    broadcastToRoom(currentRoom, 'playerLeft', {
      playerId: sock.id,
      players: getPlayersInRoom(currentRoom),
      hostId: currentRoom.hostId,
    });

    // Delete room if empty
    if (currentRoom.players.size === 0) {
      if (currentRoom.gameInterval) clearInterval(currentRoom.gameInterval);
      rooms.delete(currentRoom.id);
    }

    currentRoom = null;
    io.emit('roomList', getRoomList());
  }
});

// ─── START ───────────────────────────────────────────────────
const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`⚽ HaxFútbol server running on http://localhost:${PORT}`);
});
