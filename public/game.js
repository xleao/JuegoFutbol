/* HaxFútbol — Client with Local Prediction + Interpolation */
const socket = io();
const $ = s => document.querySelector(s);
const screens = { nickname: $('#screen-nickname'), lobby: $('#screen-lobby'), game: $('#screen-game') };

const els = {
  inputNickname: $('#input-nickname'), btnEnter: $('#btn-enter'), displayNickname: $('#display-nickname'),
  createName: $('#create-name'), createPassword: $('#create-password'), createMax: $('#create-max'),
  btnCreateRoom: $('#btn-create-room'), btnRefresh: $('#btn-refresh'), roomList: $('#room-list'),
  btnLeave: $('#btn-leave'), roomNameDisplay: $('#room-name-display'),
  scoreRed: $('#score-red'), scoreBlue: $('#score-blue'), timerDisplay: $('#timer-display'),
  teamRedList: $('#team-red-list'), teamBlueList: $('#team-blue-list'), teamSpecList: $('#team-spec-list'),
  hostControls: $('#host-controls'), btnStartGame: $('#btn-start-game'), btnStopGame: $('#btn-stop-game'),
  btnSaveSettings: $('#btn-save-settings'), settingMaxScore: $('#setting-max-score'), settingTimeLimit: $('#setting-time-limit'),
  chatLog: $('#chat-log'), chatInput: $('#chat-input'), btnSendChat: $('#btn-send-chat'),
  canvas: $('#game-canvas'), canvasWrapper: $('#canvas-wrapper'),
  gameOverlay: $('#game-overlay'), overlayContent: $('#overlay-content'),
  goalBanner: $('#goal-banner'), goalScorer: $('#goal-scorer'),
  modalPassword: $('#modal-password'), modalPasswordInput: $('#modal-password-input'),
  modalCancel: $('#modal-cancel'), modalJoin: $('#modal-join'),
  powerHud: $('#power-hud'),
  powerHudIcon: $('#power-hud-icon'),
  powerHudName: $('#power-hud-name'),
  powerHudBar: $('#power-hud-bar'),
  powerHudCooldownText: $('#power-hud-cooldown-text'),
};

let myNickname = '', myId = null, isHost = false, currentRoomId = null, gameRunning = false, pendingJoinRoomId = null;
const playerCache = new Map();
const particles = [];
const ballHistory = [];
let shakeAmount = 0;
let lastBallVx = 0;
let lastBallVy = 0;
const FIELD_W = 1200, FIELD_H = 600, GOAL_SIZE = 220, WALL_THICKNESS = 6, GOAL_DEPTH = 40, BORDER_LIMIT = 40;

// Physics constants (must match server)
const PLAYER_SPEED = 0.25, FRICTION_PLAYER = 0.94, FRICTION_BALL = 0.985;

const keys = { up: false, down: false, left: false, right: false, kick: false, power: false };
const inputHistory = [];

let clientInputSeq = 0;
let visualOffset = { x: 0, y: 0 };
const snapshotQueue = [];
const RENDER_DELAY = 85;

// ─── LOCAL PREDICTION for own player ─────────────────────────
let localPlayer = { x: 0, y: 0, vx: 0, vy: 0, radius: 18 };
let localPlayerPrev = { x: 0, y: 0 };
let localPlayerActive = false;

// ─── LOCAL BALL PREDICTION & SMOOTHING ────────────────────────
let localBall = { x: FIELD_W / 2, y: FIELD_H / 2, vx: 0, vy: 0, radius: 12 };
let localBallPrev = { x: FIELD_W / 2, y: FIELD_H / 2 };
let ballVisualOffset = { x: 0, y: 0 };

// ─── SMOOTH RENDERING FOR ENTITIES ───────────────────────────
const targetPlayers = new Map(); // player.id -> {x, y, team, radius, ping}
let targetBall = { x: FIELD_W / 2, y: FIELD_H / 2 };
let renderPlayers = [];
let renderBall = { x: FIELD_W / 2, y: FIELD_H / 2, radius: 12 };
let lastFrameTime = 0;
let physicsAccumulator = 0;
let hasReceivedFirstState = false;

// ─── CANVAS ──────────────────────────────────────────────────
const ctx = els.canvas.getContext('2d');
let canvasScale = 1, canvasOffX = 0, canvasOffY = 0;

function resizeCanvas() {
  const ww = els.canvasWrapper.clientWidth, wh = els.canvasWrapper.clientHeight;
  const totalW = FIELD_W + GOAL_DEPTH * 2 + 40, totalH = FIELD_H + 40;
  canvasScale = Math.min(ww / totalW, wh / totalH, 1.5);
  els.canvas.width = Math.floor(totalW * canvasScale);
  els.canvas.height = Math.floor(totalH * canvasScale);
  canvasOffX = (GOAL_DEPTH + 20) * canvasScale;
  canvasOffY = 20 * canvasScale;
}
window.addEventListener('resize', resizeCanvas);

function clampPlayer(player, goalTop, goalBottom) {
  const r = player.radius || 18;
  
  // Clamp Y to the absolute outer boundaries
  player.y = Math.max(-BORDER_LIMIT + r, Math.min(FIELD_H + BORDER_LIMIT - r, player.y));

  // Left boundary check
  if (player.x - r < WALL_THICKNESS) {
    if (player.y >= goalTop && player.y <= goalBottom) {
      // Inside Left Goal
      player.x = Math.max(-GOAL_DEPTH + r, player.x);
      player.y = Math.max(goalTop + r, Math.min(goalBottom - r, player.y));
    } else {
      // Outside Left Goal
      player.x = Math.max(-BORDER_LIMIT + r, player.x);
      if (player.y < goalTop) {
        player.y = Math.min(goalTop - r, player.y);
      } else {
        player.y = Math.max(goalBottom + r, player.y);
      }
    }
  }
  // Right boundary check
  else if (player.x + r > FIELD_W - WALL_THICKNESS) {
    if (player.y >= goalTop && player.y <= goalBottom) {
      // Inside Right Goal
      player.x = Math.min(FIELD_W + GOAL_DEPTH - r, player.x);
      player.y = Math.max(goalTop + r, Math.min(goalBottom - r, player.y));
    } else {
      // Outside Right Goal
      player.x = Math.min(FIELD_W + BORDER_LIMIT - r, player.x);
      if (player.y < goalTop) {
        player.y = Math.min(goalTop - r, player.y);
      } else {
        player.y = Math.max(goalBottom + r, player.y);
      }
    }
  }
}

function resolvePlayerPostCollisions(player, goalTop, goalBottom) {
  const posts = [
    { x: WALL_THICKNESS, y: goalTop, radius: 6 },
    { x: WALL_THICKNESS, y: goalBottom, radius: 6 },
    { x: FIELD_W - WALL_THICKNESS, y: goalTop, radius: 6 },
    { x: FIELD_W - WALL_THICKNESS, y: goalBottom, radius: 6 },
  ];
  posts.forEach(post => {
    const dx = player.x - post.x;
    const dy = player.y - post.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    const minDist = player.radius + post.radius;
    if (dist < minDist && dist > 0) {
      const nx = dx / dist;
      const ny = dy / dist;
      player.x = post.x + nx * minDist;
      player.y = post.y + ny * minDist;
      const dot = player.vx * nx + player.vy * ny;
      if (dot < 0) {
        player.vx -= dot * nx;
        player.vy -= dot * ny;
      }
    }
  });
}

// ─── LOCAL PLAYER PHYSICS (runs at 60Hz fixed timestep) ──────
function updateLocalPlayer(inputKeys = keys) {
  if (!localPlayerActive) return;

  let ax = 0, ay = 0;
  if (inputKeys.up) ay -= PLAYER_SPEED;
  if (inputKeys.down) ay += PLAYER_SPEED;
  if (inputKeys.left) ax -= PLAYER_SPEED;
  if (inputKeys.right) ax += PLAYER_SPEED;
  if (ax !== 0 && ay !== 0) { ax *= 0.707; ay *= 0.707; }

  localPlayer.vx += ax;
  localPlayer.vy += ay;
  localPlayer.vx *= FRICTION_PLAYER;
  localPlayer.vy *= FRICTION_PLAYER;

  // Clamp tiny velocities to zero
  if (Math.abs(localPlayer.vx) < 0.01) localPlayer.vx = 0;
  if (Math.abs(localPlayer.vy) < 0.01) localPlayer.vy = 0;

  localPlayer.x += localPlayer.vx;
  localPlayer.y += localPlayer.vy;

  // Clamp to field limits/goals and post collision resolution
  const goalTop = FIELD_H / 2 - GOAL_SIZE / 2;
  const goalBottom = FIELD_H / 2 + GOAL_SIZE / 2;
  clampPlayer(localPlayer, goalTop, goalBottom);
  resolvePlayerPostCollisions(localPlayer, goalTop, goalBottom);
}

// Gently correct local player position towards server truth
// ─── PHYSICS FUNCTIONS & COLLISIONS ──────────────────────────
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

function resolveLocalBallWallCollisions(ball) {
  const goalTop = FIELD_H / 2 - GOAL_SIZE / 2;
  const goalBottom = FIELD_H / 2 + GOAL_SIZE / 2;
  const BOUNCE_FACTOR = 0.6;

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

  // Goal posts
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
  if (ball.x < -GOAL_DEPTH) {
    ball.x = -GOAL_DEPTH;
    ball.vx *= -0.3;
  }
  if (ball.x > FIELD_W + GOAL_DEPTH) {
    ball.x = FIELD_W + GOAL_DEPTH;
    ball.vx *= -0.3;
  }
}

function updateLocalBall() {
  localBall.vx *= FRICTION_BALL;
  localBall.vy *= FRICTION_BALL;
  
  if (Math.abs(localBall.vx) < 0.01) localBall.vx = 0;
  if (Math.abs(localBall.vy) < 0.01) localBall.vy = 0;

  localBall.x += localBall.vx;
  localBall.y += localBall.vy;
}

function resolvePlayerPlayerCollisions() {
  targetPlayers.forEach((other, id) => {
    if (id === myId) return;
    if (other.team === 'spectator') return;

    const dx = other.x - localPlayer.x;
    const dy = other.y - localPlayer.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    const minDist = localPlayer.radius + (other.radius || 18);
    if (dist < minDist && dist > 0) {
      const nx = dx / dist;
      const ny = dy / dist;
      const overlap = minDist - dist;

      // Push local player back by 50% (matching the server's equal mass resolution)
      localPlayer.x -= nx * overlap * 0.5;
      localPlayer.y -= ny * overlap * 0.5;

      // Reflect local player velocity (matching server's impulse with massA=1, massB=1, bounce=0.5)
      const dvx = localPlayer.vx - (other.vx || 0);
      const dvy = localPlayer.vy - (other.vy || 0);
      const dvn = dvx * nx + dvy * ny;
      if (dvn > 0) {
        const impulse = 0.75 * dvn; // (1 + bounce) * dvn / (1/mA + 1/mB) = 1.5 * dvn / 2 = 0.75 * dvn
        localPlayer.vx -= impulse * nx;
        localPlayer.vy -= impulse * ny;
      }
    }
  });
}

function handleLocalKick(inputKeys) {
  if (!inputKeys.kick) return;
  const dx = localBall.x - localPlayer.x;
  const dy = localBall.y - localPlayer.y;
  const dist = Math.sqrt(dx * dx + dy * dy);
  const kickRange = localPlayer.radius + localBall.radius + 6;
  if (dist < kickRange) {
    const d = dist || 1;
    const PLAYER_KICK_POWER = 3.5;
    
    const kickDirX = dx / d;
    const kickDirY = dy / d;
    
    const speedProj = localBall.vx * kickDirX + localBall.vy * kickDirY;
    if (speedProj < 0) {
      localBall.vx -= speedProj * kickDirX;
      localBall.vy -= speedProj * kickDirY;
    }
    
    localBall.vx += kickDirX * PLAYER_KICK_POWER;
    localBall.vy += kickDirY * PLAYER_KICK_POWER;
  }
}

// ─── INTERPOLATION ───────────────────────────────────────────
function lerp(a, b, t) { return a + (b - a) * t; }

// ─── VFX PARTICLE SYSTEM & TRAILS ────────────────────────────
function spawnParticles(x, y, color, count, speed, sizeRange, decayRange, gravity = 0) {
  for (let i = 0; i < count; i++) {
    const angle = Math.random() * Math.PI * 2;
    const velocity = (0.3 + Math.random() * 0.7) * speed;
    particles.push({
      x,
      y,
      vx: Math.cos(angle) * velocity,
      vy: Math.sin(angle) * velocity,
      color,
      size: sizeRange[0] + Math.random() * (sizeRange[1] - sizeRange[0]),
      alpha: 1,
      decay: decayRange[0] + Math.random() * (decayRange[1] - decayRange[0]),
      gravity
    });
  }
}

function updateAndDrawParticles() {
  for (let i = particles.length - 1; i >= 0; i--) {
    const p = particles[i];
    p.x += p.vx;
    p.y += p.vy;
    p.vy += p.gravity;
    p.alpha -= p.decay;
    if (p.alpha <= 0) {
      particles.splice(i, 1);
      continue;
    }
    ctx.save();
    ctx.globalAlpha = p.alpha;
    ctx.fillStyle = p.color;
    ctx.beginPath();
    ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
  }
}

function updateBallTrail() {
  if (!renderBall) return;
  ballHistory.push({ x: renderBall.x, y: renderBall.y });
  const maxHistory = renderBall.superKicked ? 15 : 8;
  while (ballHistory.length > maxHistory) {
    ballHistory.shift();
  }

  // If ball has superKick active, spawn fire/smoke particles
  if (renderBall.superKicked) {
    const speedSq = renderBall.vx * renderBall.vx + renderBall.vy * renderBall.vy;
    const speed = Math.sqrt(speedSq || 0);
    const count = speed > 5 ? 2 : 1;
    for (let k = 0; k < count; k++) {
      const angle = speed > 0.1 ? Math.atan2(-renderBall.vy, -renderBall.vx) + (Math.random() - 0.5) * 0.7 : Math.random() * Math.PI * 2;
      const pSpeed = (0.2 + Math.random() * 0.8) * (speed * 0.35 + 1);
      const colors = ['#ef4444', '#f97316', '#fbbf24', '#fcd34d'];
      const randColor = colors[Math.floor(Math.random() * colors.length)];
      particles.push({
        x: renderBall.x + (Math.random() - 0.5) * 12,
        y: renderBall.y + (Math.random() - 0.5) * 12,
        vx: Math.cos(angle) * pSpeed,
        vy: Math.sin(angle) * pSpeed,
        color: randColor,
        size: 2 + Math.random() * 3.5,
        alpha: 1.0,
        decay: 0.02 + Math.random() * 0.04,
        gravity: 0
      });
    }
  }
}

function updatePlayerPowerEffects() {
  if (!renderPlayers) return;
  renderPlayers.forEach(p => {
    if (p.team === 'spectator') return;
    if (p.power === 'superkick' && p.powerActive) {
      // Spawn fire sparks/spores around the player
      if (Math.random() < 0.35) {
        const angle = Math.random() * Math.PI * 2;
        const px = p.x + Math.cos(angle) * p.radius;
        const py = p.y + Math.sin(angle) * p.radius;
        particles.push({
          x: px,
          y: py,
          vx: Math.cos(angle) * (0.2 + Math.random() * 0.6),
          vy: Math.sin(angle) * (0.2 + Math.random() * 0.6) - 0.25, // drift upwards slightly
          color: Math.random() < 0.55 ? '#f97316' : '#fbbf24',
          size: 1.5 + Math.random() * 2,
          alpha: 1,
          decay: 0.02 + Math.random() * 0.03,
          gravity: 0
        });
      }
    } else if (p.power === 'dash' && p.powerActive) {
      // Spawn electric blue sparks
      if (Math.random() < 0.25) {
        const angle = Math.random() * Math.PI * 2;
        const px = p.x + Math.cos(angle) * p.radius;
        const py = p.y + Math.sin(angle) * p.radius;
        particles.push({
          x: px,
          y: py,
          vx: Math.cos(angle) * (0.1 + Math.random() * 0.4),
          vy: Math.sin(angle) * (0.1 + Math.random() * 0.4),
          color: '#38bdf8',
          size: 1 + Math.random() * 2,
          alpha: 1,
          decay: 0.03 + Math.random() * 0.04,
          gravity: 0
        });
      }
    }
  });
}

function drawBallTrail() {
  if (renderBall.superKicked) {
    // Premium fire trail drawing using radial gradients per segment
    for (let i = 0; i < ballHistory.length; i++) {
      const pos = ballHistory[i];
      const alpha = (i + 1) / ballHistory.length * 0.42;
      const radius = renderBall.radius * (0.45 + 0.85 * (i + 1) / ballHistory.length);
      ctx.beginPath();
      ctx.arc(pos.x, pos.y, radius, 0, Math.PI * 2);
      const gradient = ctx.createRadialGradient(pos.x, pos.y, radius * 0.1, pos.x, pos.y, radius);
      gradient.addColorStop(0, `rgba(253, 224, 71, ${alpha})`); // yellow center
      gradient.addColorStop(0.4, `rgba(249, 115, 22, ${alpha * 0.85})`); // orange mid
      gradient.addColorStop(0.8, `rgba(239, 68, 68, ${alpha * 0.4})`); // red edge
      gradient.addColorStop(1, 'rgba(239, 68, 68, 0)');
      ctx.fillStyle = gradient;
      ctx.fill();
    }
    return;
  }

  const speedSq = renderBall.vx * renderBall.vx + renderBall.vy * renderBall.vy;
  const speed = Math.sqrt(speedSq || 0);
  if (speed < 1.2) return;
  
  for (let i = 0; i < ballHistory.length; i++) {
    const pos = ballHistory[i];
    const alpha = (i + 1) / ballHistory.length * 0.18;
    const radius = renderBall.radius * (0.4 + 0.6 * (i + 1) / ballHistory.length);
    ctx.beginPath();
    ctx.arc(pos.x, pos.y, radius, 0, Math.PI * 2);
    ctx.fillStyle = `rgba(255, 255, 255, ${alpha})`;
    ctx.fill();
  }
}

function updateRenderPositions(dt) {
  if (!hasReceivedFirstState) return;

  // Visual error offset decay for local player and ball
  visualOffset.x *= 0.85;
  visualOffset.y *= 0.85;
  if (Math.abs(visualOffset.x) < 0.01) visualOffset.x = 0;
  if (Math.abs(visualOffset.y) < 0.01) visualOffset.y = 0;

  ballVisualOffset.x *= 0.85;
  ballVisualOffset.y *= 0.85;
  if (Math.abs(ballVisualOffset.x) < 0.01) ballVisualOffset.x = 0;
  if (Math.abs(ballVisualOffset.y) < 0.01) ballVisualOffset.y = 0;

  // If there are not enough snapshots, fallback to direct positioning
  if (snapshotQueue.length < 2) {
    if (localPlayerActive) {
      const alpha = physicsAccumulator / 16.67;
      renderBall.x = lerp(localBallPrev.x, localBall.x, alpha) + ballVisualOffset.x;
      renderBall.y = lerp(localBallPrev.y, localBall.y, alpha) + ballVisualOffset.y;
      renderBall.vx = localBall.vx;
      renderBall.vy = localBall.vy;
    } else {
      renderBall.x = targetBall.x;
      renderBall.y = targetBall.y;
    }
    renderBall.superKicked = targetBall.superKicked || false;

    const newRenderPlayers = [];
    targetPlayers.forEach((target, id) => {
      let rx = target.x;
      let ry = target.y;
      if (id === myId) {
        const alpha = physicsAccumulator / 16.67;
        rx = lerp(localPlayerPrev.x, localPlayer.x, alpha) + visualOffset.x;
        ry = lerp(localPlayerPrev.y, localPlayer.y, alpha) + visualOffset.y;
      }
      newRenderPlayers.push({
        id,
        team: target.team,
        radius: target.radius,
        ping: target.ping,
        x: rx,
        y: ry,
        power: target.power,
        powerCooldown: target.powerCooldown,
        powerActive: target.powerActive
      });
    });
    renderPlayers = newRenderPlayers;
    const me = newRenderPlayers.find(p => p.id === myId);
    updateLocalPowerHUD(me);
    return;
  }

  // Calculate the time at which we want to render the remote entities
  const renderTime = performance.now() - RENDER_DELAY;

  // Find two snapshots (s0 and s1) that bracket the renderTime
  let s0 = null;
  let s1 = null;

  for (let i = 0; i < snapshotQueue.length - 1; i++) {
    const snapA = snapshotQueue[i];
    const snapB = snapshotQueue[i + 1];
    if (renderTime >= snapA.time && renderTime <= snapB.time) {
      s0 = snapA;
      s1 = snapB;
      break;
    }
  }

  // Handle boundary conditions if renderTime falls outside our queue range
  if (!s0) {
    if (renderTime < snapshotQueue[0].time) {
      s0 = snapshotQueue[0];
      s1 = snapshotQueue[0];
    } else {
      s0 = snapshotQueue[snapshotQueue.length - 1];
      s1 = snapshotQueue[snapshotQueue.length - 1];
    }
  }

  // Calculate interpolation factor
  const t = s0 === s1 ? 0 : (renderTime - s0.time) / (s1.time - s0.time);

  // 1. Interpolate or Predict Ball
  if (localPlayerActive) {
    const alpha = physicsAccumulator / 16.67;
    renderBall.x = lerp(localBallPrev.x, localBall.x, alpha) + ballVisualOffset.x;
    renderBall.y = lerp(localBallPrev.y, localBall.y, alpha) + ballVisualOffset.y;
    renderBall.vx = localBall.vx;
    renderBall.vy = localBall.vy;
    renderBall.radius = localBall.radius;
    renderBall.superKicked = targetBall.superKicked || false;
  } else {
    renderBall.x = lerp(s0.state.ball.x, s1.state.ball.x, t);
    renderBall.y = lerp(s0.state.ball.y, s1.state.ball.y, t);
    renderBall.vx = lerp(s0.state.ball.vx || 0, s1.state.ball.vx || 0, t);
    renderBall.vy = lerp(s0.state.ball.vy || 0, s1.state.ball.vy || 0, t);
    renderBall.radius = s0.state.ball.radius || 12;
    renderBall.superKicked = s0.state.ball.superKicked || false;
  }

  // 2. Interpolate Players (local uses prediction, remotes use snapshot interpolation)
  const newRenderPlayers = [];
  
  // Find all remote player IDs from the two snapshots
  const playerIds = new Set();
  s0.state.players.forEach(p => { if (p.id !== myId) playerIds.add(p.id); });
  s1.state.players.forEach(p => { if (p.id !== myId) playerIds.add(p.id); });

  // Add the local player first (using client prediction + visual offset)
  const localTarget = targetPlayers.get(myId);
  if (localTarget) {
    const alpha = physicsAccumulator / 16.67;
    const rx = lerp(localPlayerPrev.x, localPlayer.x, alpha) + visualOffset.x;
    const ry = lerp(localPlayerPrev.y, localPlayer.y, alpha) + visualOffset.y;
    newRenderPlayers.push({
      id: myId,
      team: localTarget.team,
      radius: localTarget.radius,
      ping: localTarget.ping,
      x: rx,
      y: ry,
      power: localTarget.power,
      powerCooldown: localTarget.powerCooldown,
      powerActive: localTarget.powerActive
    });
  }

  // Add the interpolated remote players
  playerIds.forEach(id => {
    const p0 = s0.state.players.find(p => p.id === id);
    const p1 = s1.state.players.find(p => p.id === id);

    if (p0 && p1) {
      newRenderPlayers.push({
        id,
        team: p0.team,
        radius: p0.radius,
        ping: p0.ping || 0,
        x: lerp(p0.x, p1.x, t),
        y: lerp(p0.y, p1.y, t),
        power: p0.power,
        powerCooldown: lerp(p0.powerCooldown || 0, p1.powerCooldown || 0, t),
        powerActive: p0.powerActive
      });
    } else if (p0) {
      newRenderPlayers.push({
        id,
        team: p0.team,
        radius: p0.radius,
        ping: p0.ping || 0,
        x: p0.x,
        y: p0.y,
        power: p0.power,
        powerCooldown: p0.powerCooldown,
        powerActive: p0.powerActive
      });
    } else if (p1) {
      newRenderPlayers.push({
        id,
        team: p1.team,
        radius: p1.radius,
        ping: p1.ping || 0,
        x: p1.x,
        y: p1.y,
        power: p1.power,
        powerCooldown: p1.powerCooldown,
        powerActive: p1.powerActive
      });
    }
  });

  renderPlayers = newRenderPlayers;
  const me = newRenderPlayers.find(p => p.id === myId);
  updateLocalPowerHUD(me);
}

// ─── RENDER LOOP ─────────────────────────────────────────────
function render(timestamp) {
  requestAnimationFrame(render);
  if (!hasReceivedFirstState) return;

  if (!lastFrameTime) lastFrameTime = timestamp;
  const dt = timestamp - lastFrameTime;
  lastFrameTime = timestamp;

  // Run local prediction with fixed timestep (60Hz / 16.67ms)
  if (localPlayerActive) {
    physicsAccumulator += dt;
    if (physicsAccumulator > 100) physicsAccumulator = 100; // Prevent death spiral on lag spikes
    while (physicsAccumulator >= 16.67) {
      localPlayerPrev.x = localPlayer.x;
      localPlayerPrev.y = localPlayer.y;
      localBallPrev.x = localBall.x;
      localBallPrev.y = localBall.y;

      clientInputSeq++;
      inputHistory.push({
        seq: clientInputSeq,
        keys: { ...keys }
      });
      if (inputHistory.length > 300) inputHistory.shift();

      // 1. Mover jugador local
      updateLocalPlayer(keys);

      // 2. Simular balón físicamente
      updateLocalBall();

      // 3. Resolvedor de Colisiones Multipaso (3 iteraciones)
      for (let iter = 0; iter < 3; iter++) {
        // A. Colisionar jugador con otros jugadores (obstáculos semi-estáticos)
        resolvePlayerPlayerCollisions();

        // B. Colisionar jugador con el balón
        resolveCircleCollisionWithMass(localPlayer, localBall, 2.5, 0.5, 0.45);

        // C. Clamp jugador local a los límites del campo / arcos y resolver postes
        const goalTop = FIELD_H / 2 - GOAL_SIZE / 2;
        const goalBottom = FIELD_H / 2 + GOAL_SIZE / 2;
        clampPlayer(localPlayer, goalTop, goalBottom);
        resolvePlayerPostCollisions(localPlayer, goalTop, goalBottom);

        // D. Colisionar balón con paredes y postes
        resolveLocalBallWallCollisions(localBall);
      }

      // 4. Patear el balón
      handleLocalKick(keys);

      if (gameRunning && localPlayerActive) {
        socket.emit('playerInput', { keys, seq: clientInputSeq });
      }

      physicsAccumulator -= 16.67;
    }
  }

  // Smoothly follow remote entities
  updateRenderPositions(dt);
  
  // Update ball trail history and player power effects
  updateBallTrail();
  updatePlayerPowerEffects();

  const s = canvasScale;
  ctx.clearRect(0, 0, els.canvas.width, els.canvas.height);
  ctx.save();
  
  // Apply Screen Shake
  if (shakeAmount > 0.05) {
    const dx = (Math.random() - 0.5) * shakeAmount;
    const dy = (Math.random() - 0.5) * shakeAmount;
    ctx.translate(dx * s, dy * s);
    shakeAmount *= 0.88; // decay
  } else {
    shakeAmount = 0;
  }
  
  ctx.translate(canvasOffX, canvasOffY);
  ctx.scale(s, s);
  
  drawField();
  
  // Draw ball trail BEFORE the ball itself
  drawBallTrail();
  
  drawBall(renderBall);
  drawPlayers(renderPlayers);
  
  // Update and draw particles
  updateAndDrawParticles();
  
  ctx.restore();
}

// ─── DRAWING ─────────────────────────────────────────────────
function drawGoalNet(x, y, w, h, isLeft) {
  ctx.save();
  ctx.fillStyle = isLeft ? 'rgba(239, 68, 68, 0.08)' : 'rgba(59, 130, 246, 0.08)';
  ctx.fillRect(x, y, w, h);
  
  ctx.strokeStyle = isLeft ? 'rgba(239, 68, 68, 0.5)' : 'rgba(59, 130, 246, 0.5)';
  ctx.lineWidth = 2.5;
  ctx.strokeRect(x, y, w, h);
  
  ctx.strokeStyle = 'rgba(255, 255, 255, 0.15)';
  ctx.lineWidth = 1;
  const spacing = 12;
  
  for (let ny = y + spacing; ny < y + h; ny += spacing) {
    ctx.beginPath(); ctx.moveTo(x, ny); ctx.lineTo(x + w, ny); ctx.stroke();
  }
  for (let nx = x + spacing; nx < x + w; nx += spacing) {
    ctx.beginPath(); ctx.moveTo(nx, y); ctx.lineTo(nx, y + h); ctx.stroke();
  }
  
  ctx.strokeStyle = isLeft ? 'rgba(239, 68, 68, 0.3)' : 'rgba(59, 130, 246, 0.3)';
  ctx.lineWidth = 1.5;
  ctx.beginPath();
  if (isLeft) {
    ctx.moveTo(x, y); ctx.lineTo(x + w, y + h / 2);
    ctx.moveTo(x, y + h); ctx.lineTo(x + w, y + h / 2);
  } else {
    ctx.moveTo(x + w, y); ctx.lineTo(x, y + h / 2);
    ctx.moveTo(x + w, y + h); ctx.lineTo(x, y + h / 2);
  }
  ctx.stroke();
  ctx.restore();
}

function drawField() {
  const w = FIELD_W, h = FIELD_H;
  const goalTop = h / 2 - GOAL_SIZE / 2, goalBot = h / 2 + GOAL_SIZE / 2;

  // Darker green grass border
  ctx.fillStyle = '#14532d';
  ctx.fillRect(-GOAL_DEPTH - 20, -BORDER_LIMIT - 20, w + GOAL_DEPTH * 2 + 40, h + BORDER_LIMIT * 2 + 40);

  // Pitch green
  ctx.fillStyle = '#1a6b35';
  ctx.fillRect(0, 0, w, h);
  ctx.fillStyle = 'rgba(0,0,0,0.04)';
  for (let x = 0; x < w; x += 160) ctx.fillRect(x, 0, 80, h);

  ctx.strokeStyle = 'rgba(255,255,255,0.3)'; ctx.lineWidth = 2;
  ctx.strokeRect(WALL_THICKNESS, WALL_THICKNESS, w - WALL_THICKNESS * 2, h - WALL_THICKNESS * 2);
  ctx.beginPath(); ctx.moveTo(w / 2, WALL_THICKNESS); ctx.lineTo(w / 2, h - WALL_THICKNESS); ctx.stroke();
  ctx.beginPath(); ctx.arc(w / 2, h / 2, 70, 0, Math.PI * 2); ctx.stroke();
  ctx.fillStyle = 'rgba(255,255,255,0.4)'; ctx.beginPath(); ctx.arc(w / 2, h / 2, 4, 0, Math.PI * 2); ctx.fill();

  ctx.strokeStyle = 'rgba(255,255,255,0.2)';
  ctx.strokeRect(WALL_THICKNESS, h / 2 - GOAL_SIZE / 2 - 40, 120, GOAL_SIZE + 80);
  ctx.strokeRect(w - WALL_THICKNESS - 120, h / 2 - GOAL_SIZE / 2 - 40, 120, GOAL_SIZE + 80);

  // Draw detailed nets
  drawGoalNet(-GOAL_DEPTH, goalTop, GOAL_DEPTH, GOAL_SIZE, true);
  drawGoalNet(w, goalTop, GOAL_DEPTH, GOAL_SIZE, false);

  ctx.fillStyle = '#2d3748';
  // Outer top and bottom walls
  ctx.fillRect(-GOAL_DEPTH - 20, -BORDER_LIMIT - 6, w + GOAL_DEPTH * 2 + 40, 6);
  ctx.fillRect(-GOAL_DEPTH - 20, h + BORDER_LIMIT, w + GOAL_DEPTH * 2 + 40, 6);

  // Left vertical walls
  ctx.fillRect(-BORDER_LIMIT - 6, -BORDER_LIMIT - 6, 6, BORDER_LIMIT + goalTop + 6);
  ctx.fillRect(-BORDER_LIMIT - 6, goalBot, 6, h - goalBot + BORDER_LIMIT + 6);

  // Right vertical walls
  ctx.fillRect(w + BORDER_LIMIT, -BORDER_LIMIT - 6, 6, BORDER_LIMIT + goalTop + 6);
  ctx.fillRect(w + BORDER_LIMIT, goalBot, 6, h - goalBot + BORDER_LIMIT + 6);

  // Goal structures (backs, tops, bottoms)
  ctx.fillRect(-GOAL_DEPTH - 6, goalTop, 6, goalBot - goalTop); // Left goal back
  ctx.fillRect(-GOAL_DEPTH, goalTop - 3, GOAL_DEPTH + WALL_THICKNESS, 3); // Left goal top
  ctx.fillRect(-GOAL_DEPTH, goalBot, GOAL_DEPTH + WALL_THICKNESS, 3); // Left goal bottom

  ctx.fillRect(w + GOAL_DEPTH, goalTop, 6, goalBot - goalTop); // Right goal back
  ctx.fillRect(w - WALL_THICKNESS, goalTop - 3, GOAL_DEPTH + WALL_THICKNESS, 3); // Right goal top
  ctx.fillRect(w - WALL_THICKNESS, goalBot, GOAL_DEPTH + WALL_THICKNESS, 3); // Right goal bottom

  [{ x: WALL_THICKNESS, y: goalTop }, { x: WALL_THICKNESS, y: goalBot }, { x: w - WALL_THICKNESS, y: goalTop }, { x: w - WALL_THICKNESS, y: goalBot }].forEach(p => {
    ctx.beginPath(); ctx.arc(p.x, p.y, 6, 0, Math.PI * 2);
    ctx.fillStyle = '#e2e8f0'; ctx.fill();
    ctx.strokeStyle = '#94a3b8'; ctx.lineWidth = 2; ctx.stroke();
  });
}

function drawBall(ball) {
  if (!ball) return;
  // Improved shadow
  ctx.beginPath(); ctx.arc(ball.x + 4, ball.y + 6, ball.radius, 0, Math.PI * 2); ctx.fillStyle = 'rgba(0,0,0,0.25)'; ctx.fill();
  
  // Outer fire glow if superKicked
  if (ball.superKicked) {
    ctx.save();
    const glowRadius = ball.radius + 6 + Math.sin(Date.now() / 70) * 2.5;
    ctx.beginPath();
    ctx.arc(ball.x, ball.y, glowRadius, 0, Math.PI * 2);
    const glowGradient = ctx.createRadialGradient(ball.x, ball.y, ball.radius * 0.75, ball.x, ball.y, glowRadius);
    glowGradient.addColorStop(0, 'rgba(253, 224, 71, 0.95)'); // Bright yellow center
    glowGradient.addColorStop(0.4, 'rgba(249, 115, 22, 0.75)'); // Fiery orange mid
    glowGradient.addColorStop(1, 'rgba(239, 68, 68, 0)'); // Transparent red outer
    ctx.fillStyle = glowGradient;
    ctx.fill();
    ctx.restore();
  }

  ctx.beginPath(); ctx.arc(ball.x, ball.y, ball.radius, 0, Math.PI * 2);
  const g = ctx.createRadialGradient(ball.x - 3, ball.y - 3, 1, ball.x, ball.y, ball.radius);
  g.addColorStop(0, ball.superKicked ? '#fef08a' : '#ffffff');
  g.addColorStop(1, ball.superKicked ? '#ea580c' : '#d1d5db');
  ctx.fillStyle = g; ctx.fill();
  ctx.strokeStyle = ball.superKicked ? '#ea580c' : '#9ca3af'; ctx.lineWidth = ball.superKicked ? 2.5 : 1.5; ctx.stroke();
  
  ctx.fillStyle = ball.superKicked ? 'rgba(254, 240, 138, 0.35)' : 'rgba(0,0,0,0.12)';
  ctx.beginPath(); ctx.arc(ball.x, ball.y, ball.radius * 0.45, 0, Math.PI * 2); ctx.fill();
}

function drawPlayers(players) {
  if (!players) return;
  players.forEach(p => {
    if (p.team === 'spectator') return;
    const isMe = p.id === myId;
    const tc = p.team === 'red' ? '#ef4444' : '#3b82f6';
    const tl = p.team === 'red' ? '#fca5a5' : '#93c5fd';
    const td = p.team === 'red' ? '#b91c1c' : '#1d4ed8';

    // Improved soft shadow
    ctx.beginPath(); ctx.arc(p.x + 3, p.y + 5, p.radius, 0, Math.PI * 2); ctx.fillStyle = 'rgba(0,0,0,0.22)'; ctx.fill();
    
    // Active power glowing ring underneath player
    if (p.powerActive) {
      ctx.save();
      const activeRadius = p.radius + 6 + Math.sin(Date.now() / 100) * 2.5;
      ctx.beginPath();
      ctx.arc(p.x, p.y, activeRadius, 0, Math.PI * 2);
      ctx.strokeStyle = p.power === 'superkick' ? 'rgba(249, 115, 22, 0.85)' : 'rgba(14, 165, 233, 0.85)';
      ctx.lineWidth = 3;
      ctx.shadowBlur = 12;
      ctx.shadowColor = p.power === 'superkick' ? '#f97316' : '#0ea5e9';
      ctx.stroke();
      
      // Secondary aura
      ctx.beginPath();
      ctx.arc(p.x, p.y, activeRadius + 2.5, 0, Math.PI * 2);
      ctx.strokeStyle = p.power === 'superkick' ? 'rgba(239, 68, 68, 0.35)' : 'rgba(59, 130, 246, 0.35)';
      ctx.lineWidth = 1.5;
      ctx.stroke();
      ctx.restore();
    }

    // Cooldown indicator ring
    if (p.powerCooldown > 0 && !p.powerActive) {
      const cdRadius = p.radius + 5;
      ctx.beginPath();
      ctx.arc(p.x, p.y, cdRadius, 0, Math.PI * 2);
      ctx.strokeStyle = 'rgba(0,0,0,0.25)';
      ctx.lineWidth = 3.5;
      ctx.stroke();

      const maxCd = 5.0; // max cooldown is 5s
      const angle = (p.powerCooldown / maxCd) * Math.PI * 2;
      ctx.beginPath();
      ctx.arc(p.x, p.y, cdRadius, -Math.PI / 2, -Math.PI / 2 + angle, false);
      ctx.strokeStyle = '#ef4444';
      ctx.lineWidth = 3.5;
      ctx.lineCap = 'round';
      ctx.stroke();
    }

    // Draw main player body
    ctx.beginPath(); ctx.arc(p.x, p.y, p.radius, 0, Math.PI * 2);
    const g = ctx.createRadialGradient(p.x - 4, p.y - 4, 2, p.x, p.y, p.radius);
    g.addColorStop(0, tl); g.addColorStop(1, tc); ctx.fillStyle = g; ctx.fill();
    ctx.strokeStyle = isMe ? '#22d3ee' : td; ctx.lineWidth = isMe ? 3 : 2; ctx.stroke();

    if (isMe) {
      ctx.beginPath(); ctx.arc(p.x, p.y, p.radius + 4, 0, Math.PI * 2);
      ctx.strokeStyle = 'rgba(34,211,238,0.35)'; ctx.lineWidth = 2; ctx.stroke();
    }

    // Resolve nickname from cache
    const cached = playerCache.get(p.id);
    const nicknameStr = cached ? cached.nickname : (p.nickname || 'Jugador');

    ctx.fillStyle = '#fff';
    ctx.font = `bold ${isMe ? 11 : 10}px Inter,sans-serif`;
    ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
    ctx.shadowColor = 'rgba(0,0,0,0.7)'; ctx.shadowBlur = 3;
    ctx.fillText(nicknameStr, p.x, p.y - p.radius - 6);
    ctx.shadowBlur = 0;
  });
}

// ─── INPUT ───────────────────────────────────────────────────
const keyMap = { ArrowUp: 'up', w: 'up', W: 'up', ArrowDown: 'down', s: 'down', S: 'down', ArrowLeft: 'left', a: 'left', A: 'left', ArrowRight: 'right', d: 'right', D: 'right', ' ': 'kick', x: 'kick', X: 'kick', Shift: 'power', q: 'power', Q: 'power', e: 'power', E: 'power' };

document.addEventListener('keydown', e => {
  if (e.target.tagName === 'INPUT') return;
  const a = keyMap[e.key]; if (a) { e.preventDefault(); keys[a] = true; }
});
document.addEventListener('keyup', e => {
  if (e.target.tagName === 'INPUT') return;
  const a = keyMap[e.key]; if (a) { keys[a] = false; }
});

// ─── SCREENS & UI ────────────────────────────────────────────
function showScreen(name) { Object.values(screens).forEach(s => s.classList.remove('active')); screens[name].classList.add('active'); if (name === 'game') resizeCanvas(); }
function escapeHtml(s) { const d = document.createElement('div'); d.textContent = s; return d.innerHTML; }

els.btnEnter.addEventListener('click', enterLobby);
els.inputNickname.addEventListener('keydown', e => { if (e.key === 'Enter') enterLobby(); });
function enterLobby() { const n = els.inputNickname.value.trim(); if (!n) { els.inputNickname.style.borderColor = '#ef4444'; return; } myNickname = n; socket.emit('setNickname', n); els.displayNickname.textContent = n; showScreen('lobby'); socket.emit('getRooms'); }

els.btnCreateRoom.addEventListener('click', () => {
  const pwr = $('#select-power') ? $('#select-power').value : 'superkick';
  console.log(`[CLIENT DEBUG] btnCreateRoom: selected power value = "${pwr}"`);
  socket.emit('createRoom', { name: els.createName.value.trim() || 'Sala de ' + myNickname, password: els.createPassword.value.trim(), maxPlayers: parseInt(els.createMax.value) || 10, power: pwr });
});
els.btnRefresh.addEventListener('click', () => socket.emit('getRooms'));

socket.on('roomList', rooms => {
  if (!rooms.length) { els.roomList.innerHTML = '<p class="room-empty">No hay salas. ¡Crea una!</p>'; return; }
  els.roomList.innerHTML = rooms.map(r => `<div class="room-item"><div class="room-item-info"><span class="room-item-name">${escapeHtml(r.name)}</span><div class="room-item-meta">${r.hasPassword ? '<span class="room-lock">🔒</span>' : ''}${r.gameRunning ? `<span class="room-playing">⚽ ${r.scoreRed}-${r.scoreBlue}</span>` : '<span>En espera</span>'}</div></div><div class="room-item-right"><span class="room-players-count">${r.playerCount}/${r.maxPlayers}</span><button class="btn-join-room" data-rid="${r.id}" data-pw="${r.hasPassword}">UNIRSE</button></div></div>`).join('');
  els.roomList.querySelectorAll('.btn-join-room').forEach(b => b.addEventListener('click', e => { e.stopPropagation(); joinRoom(b.dataset.rid, b.dataset.pw === 'true'); }));
});

function joinRoom(rid, hasPw) {
  const pwr = $('#select-power') ? $('#select-power').value : 'superkick';
  console.log(`[CLIENT DEBUG] joinRoom: selected power value = "${pwr}"`);
  if (hasPw) {
    pendingJoinRoomId = rid;
    els.modalPassword.classList.remove('hidden');
    els.modalPasswordInput.value = '';
    els.modalPasswordInput.focus();
  } else {
    socket.emit('joinRoom', { roomId: rid, password: '', power: pwr });
  }
}
els.modalCancel.addEventListener('click', () => { els.modalPassword.classList.add('hidden'); pendingJoinRoomId = null; });
els.modalJoin.addEventListener('click', () => {
  if (pendingJoinRoomId) {
    const pwr = $('#select-power') ? $('#select-power').value : 'superkick';
    socket.emit('joinRoom', { roomId: pendingJoinRoomId, password: els.modalPasswordInput.value, power: pwr });
    els.modalPassword.classList.add('hidden');
    pendingJoinRoomId = null;
  }
});
els.modalPasswordInput.addEventListener('keydown', e => { if (e.key === 'Enter') els.modalJoin.click(); });
socket.on('joinError', msg => alert(msg));

socket.on('connect', () => { myId = socket.id; });

socket.on('roomJoined', data => {
  myId = socket.id;
  currentRoomId = data.roomId; isHost = data.isHost;
  els.roomNameDisplay.textContent = data.roomName;
  els.settingMaxScore.value = data.maxScore || 5; els.settingTimeLimit.value = data.timeLimit || 180;
  gameRunning = !!data.gameRunning; hasReceivedFirstState = false; targetPlayers.clear(); renderPlayers = []; localPlayerActive = false;
  localPlayerPrev.x = 0; localPlayerPrev.y = 0;
  inputHistory.length = 0;
  snapshotQueue.length = 0;
  clientInputSeq = 0;
  visualOffset.x = 0;
  visualOffset.y = 0;
  localBall.x = FIELD_W / 2; localBall.y = FIELD_H / 2;
  localBall.vx = 0; localBall.vy = 0;
  localBallPrev.x = FIELD_W / 2; localBallPrev.y = FIELD_H / 2;
  ballVisualOffset.x = 0; ballVisualOffset.y = 0;
  els.chatLog.innerHTML = ''; els.scoreRed.textContent = '0'; els.scoreBlue.textContent = '0'; els.timerDisplay.textContent = '0:00';
  updateHostUI(); updatePlayerLists(data.players); showScreen('game');
  if (gameRunning) {
    hideOverlay();
  } else {
    showOverlay('Esperando jugadores...\n\nWASD / Flechas = moverse\nESPACIO / X = patear');
  }
});

socket.on('playerJoined', d => updatePlayerLists(d.players));
socket.on('playerLeft', d => { updatePlayerLists(d.players); if (d.hostId === myId) { isHost = true; updateHostUI(); } });
socket.on('playerChangedTeam', d => updatePlayerLists(d.players));
socket.on('settingsUpdated', d => { els.settingMaxScore.value = d.maxScore; els.settingTimeLimit.value = d.timeLimit; });
socket.on('gameStarted', () => { gameRunning = true; localPlayerActive = true; hideOverlay(); updateHostUI(); });

socket.on('gameEnded', d => {
  gameRunning = false; localPlayerActive = false; updateHostUI();
  let m = d.winner === 'red' ? '🔴 ¡ROJO GANA! 🏆' : d.winner === 'blue' ? '🔵 ¡AZUL GANA! 🏆' : d.winner === 'draw' ? '🤝 ¡EMPATE!' : '⏹ Juego detenido';
  showOverlay(m + `\n\n${d.scoreRed} - ${d.scoreBlue}`);
});

socket.on('goalScored', d => {
  els.scoreRed.textContent = d.scoreRed; els.scoreBlue.textContent = d.scoreBlue;
  els.goalScorer.textContent = d.scorer; els.goalBanner.classList.remove('hidden');
  setTimeout(() => els.goalBanner.classList.add('hidden'), 2000);

  // Confetti effect at the scored goal (opposite of scoring team)
  const confettiX = d.team === 'blue' ? 10 : FIELD_W - 10;
  const confettiY = FIELD_H / 2;
  const colors = ['#f43f5e', '#3b82f6', '#10b981', '#eab308', '#a855f7', '#ec4899', '#f97316'];
  for (let i = 0; i < 70; i++) {
    const randColor = colors[Math.floor(Math.random() * colors.length)];
    const angle = d.team === 'blue' ? (Math.random() * 0.6 - 0.3) * Math.PI : (Math.random() * 0.6 + 0.7) * Math.PI;
    const velocity = 3 + Math.random() * 6;
    particles.push({
      x: confettiX,
      y: confettiY + (Math.random() - 0.5) * GOAL_SIZE,
      vx: Math.cos(angle) * velocity,
      vy: Math.sin(angle) * velocity - (2 + Math.random() * 3),
      color: randColor,
      size: 2 + Math.random() * 3,
      alpha: 1,
      decay: 0.01 + Math.random() * 0.012,
      gravity: 0.12
    });
  }
  shakeAmount = 18;
});

socket.on('playerSuperkick', data => {
  const p = targetPlayers.get(data.playerId);
  if (p) {
    spawnParticles(p.x, p.y, '#f97316', 15, 4, [2, 4], [0.02, 0.05]);
    spawnParticles(p.x, p.y, '#fbbf24', 10, 3, [1.5, 3.5], [0.03, 0.06]);
  }
  shakeAmount = Math.min(shakeAmount + 12, 20);
});

socket.on('playerDash', data => {
  spawnParticles(data.x, data.y, '#0ea5e9', 15, 3.5, [2, 4], [0.03, 0.06]);
  spawnParticles(data.x, data.y, '#38bdf8', 10, 2.5, [1.5, 3.5], [0.04, 0.08]);
  shakeAmount = Math.min(shakeAmount + 4, 8);
});

socket.on('superkickImpact', data => {
  spawnParticles(data.x, data.y, '#ef4444', 25, 6, [3, 5], [0.015, 0.04]);
  spawnParticles(data.x, data.y, '#f97316', 15, 4.5, [2, 4], [0.02, 0.05]);
  spawnParticles(data.x, data.y, '#fcd34d', 10, 3, [1.5, 3], [0.03, 0.06]);
  shakeAmount = Math.min(shakeAmount + 24, 30);
});

function updateLocalPowerHUD(player) {
  if (player) {
    console.log(`[CLIENT DEBUG] updateLocalPowerHUD: player.power = "${player.power}", cooldown = ${player.powerCooldown}, active = ${player.powerActive}`);
  }
  if (!player || player.team === 'spectator' || !gameRunning) {
    if (els.powerHud) els.powerHud.classList.add('hidden');
    return;
  }

  if (els.powerHud) els.powerHud.classList.remove('hidden');

  const pName = player.power === 'superkick' ? 'Supertiro' : 'Dash';
  const pIcon = player.power === 'superkick' ? '🔥' : '⚡';

  if (els.powerHudName) els.powerHudName.textContent = pName;
  if (els.powerHudIcon) els.powerHudIcon.textContent = pIcon;

  if (player.powerActive) {
    if (els.powerHud) els.powerHud.classList.add('active-glowing');
    if (els.powerHudBar) {
      els.powerHudBar.style.width = '100%';
      els.powerHudBar.style.background = player.power === 'superkick' ? 'linear-gradient(90deg, #f97316, #ef4444)' : 'linear-gradient(90deg, #0ea5e9, #3b82f6)';
    }
    if (els.powerHudCooldownText) {
      els.powerHudCooldownText.textContent = player.power === 'superkick' ? '¡SÚPER TIRO CARGADO!' : '¡TELETRANSPORTE!';
    }
  } else if (player.powerCooldown > 0) {
    if (els.powerHud) els.powerHud.classList.remove('active-glowing');
    const cdPercent = Math.max(0, Math.min(100, (1 - player.powerCooldown / 5.0) * 100));
    if (els.powerHudBar) {
      els.powerHudBar.style.width = `${cdPercent}%`;
      els.powerHudBar.style.background = '#ef4444';
    }
    if (els.powerHudCooldownText) {
      els.powerHudCooldownText.textContent = `ESPERA: ${player.powerCooldown.toFixed(1)}s`;
    }
  } else {
    if (els.powerHud) els.powerHud.classList.remove('active-glowing');
    if (els.powerHudBar) {
      els.powerHudBar.style.width = '100%';
      els.powerHudBar.style.background = '#10b981';
    }
    if (els.powerHudCooldownText) {
      els.powerHudCooldownText.textContent = 'DISPONIBLE [Shift]';
    }
  }
}

// ─── SERVER SNAPSHOTS (20Hz) ─────────────────────────────────
socket.on('gameState', state => {
  hasReceivedFirstState = true;

  // Store snapshot in queue with local time
  snapshotQueue.push({
    time: performance.now(),
    state: state
  });
  if (snapshotQueue.length > 30) {
    snapshotQueue.shift();
  }

  // Update targets
  targetBall.x = state.ball.x;
  targetBall.y = state.ball.y;
  targetBall.vx = state.ball.vx;
  targetBall.vy = state.ball.vy;
  targetBall.superKicked = state.ball.superKicked || false;
  
  // Clean up targetPlayers not in the new snapshot
  const currentIds = new Set(state.players.map(p => p.id));
  for (const id of targetPlayers.keys()) {
    if (!currentIds.has(id)) {
      targetPlayers.delete(id);
    }
  }

  // Update target players
  state.players.forEach(p => {
    targetPlayers.set(p.id, {
      x: p.x,
      y: p.y,
      vx: p.vx,
      vy: p.vy,
      team: p.team,
      radius: p.radius,
      ping: p.ping || 0,
      power: p.power,
      powerCooldown: p.powerCooldown,
      powerActive: p.powerActive
    });
  });

  // Update ping and map cache
  state.players.forEach(p => {
    const cached = playerCache.get(p.id);
    if (cached) {
      cached.ping = p.ping || 0;
    }
    const pingEl = document.getElementById(`ping-${p.id}`);
    if (pingEl) {
      const pingVal = p.ping || 0;
      pingEl.textContent = `${pingVal}ms`;
      pingEl.style.color = pingVal < 70 ? '#10b981' : (pingVal < 150 ? '#fbbf24' : '#ef4444');
    }
  });

  // Detect ball velocity changes for impact VFX
  const cb = state.ball;
  if (cb) {
    const dvx = cb.vx - lastBallVx;
    const dvy = cb.vy - lastBallVy;
    const deltaSpeed = Math.sqrt(dvx * dvx + dvy * dvy);
    
    if (deltaSpeed > 1.2) {
      let sparkColor = '#fcd34d'; // yellow sparks default
      let closestPlayer = null;
      let minDist = 9999;
      state.players.forEach(p => {
        const dx = p.x - cb.x;
        const dy = p.y - cb.y;
        const d = Math.sqrt(dx * dx + dy * dy);
        if (d < minDist) {
          minDist = d;
          closestPlayer = p;
        }
      });
      
      if (closestPlayer && minDist < closestPlayer.radius + cb.radius + 15) {
        // Player kicked or hit ball
        const cached = playerCache.get(closestPlayer.id);
        const team = cached ? cached.team : closestPlayer.team;
        sparkColor = team === 'red' ? '#fca5a5' : '#93c5fd';
        spawnParticles(cb.x, cb.y, sparkColor, 12, 3.5, [1.5, 3.2], [0.03, 0.06]);
        shakeAmount = Math.min(shakeAmount + deltaSpeed * 1.4, 7);
      } else {
        // Wall or post bounce
        spawnParticles(cb.x, cb.y, '#e2e8f0', 8, 2.5, [1, 2.5], [0.04, 0.08]);
        shakeAmount = Math.min(shakeAmount + deltaSpeed * 0.8, 4.5);
      }
    }
    lastBallVx = cb.vx;
    lastBallVy = cb.vy;
  }

  // Correct local player and ball towards server position (Input Reconciliation)
  const me = state.players.find(p => p.id === myId);
  if (me) {
    if (!localPlayerActive) {
      localPlayer.x = me.x; localPlayer.y = me.y;
      localPlayer.vx = me.vx; localPlayer.vy = me.vy;
      localPlayer.radius = me.radius;
      localPlayerPrev.x = me.x; localPlayerPrev.y = me.y;
      localPlayerActive = true;
      visualOffset.x = 0; visualOffset.y = 0;

      localBall.x = state.ball.x; localBall.y = state.ball.y;
      localBall.vx = state.ball.vx; localBall.vy = state.ball.vy;
      localBall.radius = state.ball.radius || 12;
      localBallPrev.x = state.ball.x; localBallPrev.y = state.ball.y;
      ballVisualOffset.x = 0; ballVisualOffset.y = 0;
    } else {
      // 1. Keep track of current predicted positions before reconciliation
      const oldX = localPlayer.x;
      const oldY = localPlayer.y;
      const oldBallX = localBall.x;
      const oldBallY = localBall.y;

      // 2. Reset local player and ball state to server snapshot
      localPlayer.x = me.x;
      localPlayer.y = me.y;
      localPlayer.vx = me.vx;
      localPlayer.vy = me.vy;
      localPlayer.radius = me.radius;

      localBall.x = state.ball.x;
      localBall.y = state.ball.y;
      localBall.vx = state.ball.vx;
      localBall.vy = state.ball.vy;
      localBall.radius = state.ball.radius || 12;

      // 3. Remove all inputs acknowledged by the server
      const serverSeq = me.lastProcessedSeq || 0;
      while (inputHistory.length > 0 && inputHistory[0].seq <= serverSeq) {
        inputHistory.shift();
      }

      // 4. Replay all remaining unacknowledged inputs (re-simulating both player and ball!)
      inputHistory.forEach(item => {
        updateLocalPlayer(item.keys);
        updateLocalBall();
        for (let iter = 0; iter < 3; iter++) {
          resolvePlayerPlayerCollisions();
          resolveCircleCollisionWithMass(localPlayer, localBall, 2.5, 0.5, 0.45);
          const goalTop = FIELD_H / 2 - GOAL_SIZE / 2;
          const goalBottom = FIELD_H / 2 + GOAL_SIZE / 2;
          clampPlayer(localPlayer, goalTop, goalBottom);
          resolvePlayerPostCollisions(localPlayer, goalTop, goalBottom);
          resolveLocalBallWallCollisions(localBall);
        }
        handleLocalKick(item.keys);
      });

      // 5. Update the visual offset to smooth out prediction errors
      const diffX = oldX - localPlayer.x;
      const diffY = oldY - localPlayer.y;
      
      // If there's a massive teleport (like goal kickoff reset), don't smooth it, just snap
      if (Math.abs(diffX) > 120 || Math.abs(diffY) > 120) {
        visualOffset.x = 0;
        visualOffset.y = 0;
        localPlayerPrev.x = localPlayer.x;
        localPlayerPrev.y = localPlayer.y;
      } else {
        visualOffset.x += diffX;
        visualOffset.y += diffY;
        
        // Correctly align the interpolation base to keep prediction interpolation working
        localPlayerPrev.x = localPlayer.x - localPlayer.vx;
        localPlayerPrev.y = localPlayer.y - localPlayer.vy;
      }

      // 6. Update the ball's visual offset to smooth out ball prediction errors
      const diffBallX = oldBallX - localBall.x;
      const diffBallY = oldBallY - localBall.y;

      if (Math.abs(diffBallX) > 150 || Math.abs(diffBallY) > 150) {
        ballVisualOffset.x = 0;
        ballVisualOffset.y = 0;
        localBallPrev.x = localBall.x;
        localBallPrev.y = localBall.y;
      } else {
        ballVisualOffset.x += diffBallX;
        ballVisualOffset.y += diffBallY;

        localBallPrev.x = localBall.x - localBall.vx;
        localBallPrev.y = localBall.y - localBall.vy;
      }
    }
  }

  els.scoreRed.textContent = state.scoreRed;
  els.scoreBlue.textContent = state.scoreBlue;
  if (state.timeLimit > 0) {
    const rem = Math.max(0, state.timeLimit - state.gameTimer);
    els.timerDisplay.textContent = `${Math.floor(rem / 60)}:${(rem % 60).toString().padStart(2, '0')}`;
  } else {
    els.timerDisplay.textContent = `${Math.floor(state.gameTimer / 60)}:${(state.gameTimer % 60).toString().padStart(2, '0')}`;
  }
});

socket.on('kicked', msg => { alert(msg); currentRoomId = null; gameRunning = false; hasReceivedFirstState = false; targetPlayers.clear(); renderPlayers = []; localPlayerActive = false; showScreen('lobby'); socket.emit('getRooms'); });

document.querySelectorAll('.btn-team').forEach(b => b.addEventListener('click', () => socket.emit('changeTeam', b.dataset.team)));

function updatePlayerLists(players) {
  // Update local player cache map
  playerCache.clear();
  players.forEach(p => {
    playerCache.set(p.id, {
      nickname: p.nickname,
      team: p.team,
      isHost: p.isHost,
      goals: p.goals || 0,
      ping: p.ping || 0
    });
  });

  const r = players.filter(p => p.team === 'red'), b = players.filter(p => p.team === 'blue'), s = players.filter(p => p.team === 'spectator');
  els.teamRedList.innerHTML = r.map(p => playerHTML(p)).join('');
  els.teamBlueList.innerHTML = b.map(p => playerHTML(p)).join('');
  els.teamSpecList.innerHTML = s.map(p => playerHTML(p)).join('');
  if (isHost) document.querySelectorAll('.player-kick-btn').forEach(b => b.addEventListener('click', () => socket.emit('kickPlayer', b.dataset.playerId)));
}
function playerHTML(p) {
  const host = p.isHost ? '<span class="player-host">★ HOST</span>' : '';
  const kick = (isHost && p.id !== myId) ? `<button class="player-kick-btn" data-player-id="${p.id}">✕</button>` : '';
  const pingVal = playerCache.get(p.id)?.ping || p.ping || 0;
  const pingColor = pingVal < 70 ? '#10b981' : (pingVal < 150 ? '#fbbf24' : '#ef4444');
  const pingSpan = `<span class="player-ping" id="ping-${p.id}" style="color:${pingColor}; font-size: 0.75rem; margin-left: 6px; font-variant-numeric: tabular-nums;">${pingVal}ms</span>`;
  return `<div class="team-player"><span class="player-name">${escapeHtml(p.nickname)}${p.id === myId ? ' (tú)' : ''}${pingSpan}</span><span>${host}${kick}</span></div>`;
}

function updateHostUI() { els.hostControls.style.display = isHost ? 'block' : 'none'; els.btnStartGame.style.display = gameRunning ? 'none' : 'block'; els.btnStopGame.style.display = gameRunning ? 'block' : 'none'; }
els.btnStartGame.addEventListener('click', () => socket.emit('startGame'));
els.btnStopGame.addEventListener('click', () => socket.emit('stopGame'));
els.btnSaveSettings.addEventListener('click', () => socket.emit('updateSettings', { maxScore: parseInt(els.settingMaxScore.value) || 5, timeLimit: parseInt(els.settingTimeLimit.value) || 0 }));
els.btnLeave.addEventListener('click', () => { socket.emit('leaveRoom'); currentRoomId = null; gameRunning = false; hasReceivedFirstState = false; targetPlayers.clear(); renderPlayers = []; localPlayerActive = false; showScreen('lobby'); socket.emit('getRooms'); });

els.btnSendChat.addEventListener('click', sendChat);
els.chatInput.addEventListener('keydown', e => { if (e.key === 'Enter') sendChat(); });
function sendChat() { const m = els.chatInput.value.trim(); if (!m) return; socket.emit('chatMessage', m); els.chatInput.value = ''; }
socket.on('chatMessage', d => {
  const div = document.createElement('div'); div.className = 'chat-msg';
  if (d.type === 'system') { div.classList.add('chat-msg-system'); div.textContent = d.message; }
  else { div.classList.add('chat-msg-player'); div.innerHTML = `<span class="chat-nick chat-nick-${d.team}">${escapeHtml(d.nickname)}:</span> ${escapeHtml(d.message)}`; }
  els.chatLog.appendChild(div); els.chatLog.scrollTop = els.chatLog.scrollHeight;
  while (els.chatLog.children.length > 100) els.chatLog.removeChild(els.chatLog.firstChild);
});

function showOverlay(t) { els.overlayContent.classList.remove('hidden'); els.overlayContent.innerHTML = `<p>${t.replace(/\n/g, '<br>')}</p>`; }
function hideOverlay() { els.overlayContent.classList.add('hidden'); }

requestAnimationFrame(render);
setInterval(() => { if (screens.lobby.classList.contains('active')) socket.emit('getRooms'); }, 5000);

// ─── PING/PONG LOOP ──────────────────────────────────────────
setInterval(() => {
  if (currentRoomId) {
    socket.emit('pingRequest', { clientTime: Date.now() });
  }
}, 2000);

socket.on('pingResponse', data => {
  if (data && data.clientTime) {
    const pingVal = Date.now() - data.clientTime;
    socket.emit('pingUpdate', pingVal);
  }
});
