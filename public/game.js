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
};

let myNickname = '', myId = null, isHost = false, currentRoomId = null, gameRunning = false, pendingJoinRoomId = null;
const FIELD_W = 1200, FIELD_H = 600, GOAL_SIZE = 160, WALL_THICKNESS = 6, GOAL_DEPTH = 40;

// Physics constants (must match server)
const PLAYER_SPEED = 1.4, FRICTION_PLAYER = 0.84, FRICTION_BALL = 0.99;

const keys = { up: false, down: false, left: false, right: false, kick: false };
let lastSentInput = '';

// ─── LOCAL PREDICTION for own player ─────────────────────────
let localPlayer = { x: 0, y: 0, vx: 0, vy: 0, radius: 18 };
let localPlayerActive = false;

// ─── INTERPOLATION for remote entities ───────────────────────
let prevSnapshot = null, curSnapshot = null, snapshotTime = 0;
const SNAPSHOT_INTERVAL = 1000 / 20;
let renderPlayers = [];
let renderBall = { x: FIELD_W / 2, y: FIELD_H / 2, radius: 12 };
let lastFrameTime = 0;

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

// ─── LOCAL PLAYER PHYSICS (runs every frame at 60fps) ────────
function updateLocalPlayer(dt) {
  if (!localPlayerActive) return;

  let ax = 0, ay = 0;
  if (keys.up) ay -= PLAYER_SPEED;
  if (keys.down) ay += PLAYER_SPEED;
  if (keys.left) ax -= PLAYER_SPEED;
  if (keys.right) ax += PLAYER_SPEED;
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

  // Clamp to field
  localPlayer.x = Math.max(localPlayer.radius + WALL_THICKNESS, Math.min(FIELD_W - localPlayer.radius - WALL_THICKNESS, localPlayer.x));
  localPlayer.y = Math.max(localPlayer.radius + WALL_THICKNESS, Math.min(FIELD_H - localPlayer.radius - WALL_THICKNESS, localPlayer.y));
}

// Gently correct local player position towards server truth
function correctLocalPlayer(serverX, serverY) {
  if (!localPlayerActive) {
    localPlayer.x = serverX;
    localPlayer.y = serverY;
    return;
  }
  const correctionStrength = 0.15; // Blend 15% towards server each snapshot
  localPlayer.x += (serverX - localPlayer.x) * correctionStrength;
  localPlayer.y += (serverY - localPlayer.y) * correctionStrength;
}

// ─── INTERPOLATION ───────────────────────────────────────────
function lerp(a, b, t) { return a + (b - a) * t; }

function interpolateRemotes(now) {
  if (!curSnapshot) return;
  if (!prevSnapshot) prevSnapshot = curSnapshot;

  const elapsed = now - snapshotTime;
  let t = Math.min(elapsed / SNAPSHOT_INTERVAL, 1.5);

  // Ball interpolation
  const cb = curSnapshot.ball, pb = prevSnapshot.ball;
  if (cb && pb) {
    if (t <= 1) {
      renderBall.x = lerp(pb.x, cb.x, t);
      renderBall.y = lerp(pb.y, cb.y, t);
    } else {
      const extra = (t - 1) * SNAPSHOT_INTERVAL / 16.67;
      renderBall.x = cb.x + (cb.vx || 0) * extra * FRICTION_BALL;
      renderBall.y = cb.y + (cb.vy || 0) * extra * FRICTION_BALL;
    }
    renderBall.radius = cb.radius;
  }

  // Build render list: interpolate remote players, use local for self
  renderPlayers = curSnapshot.players.map(cp => {
    // Local player: use predicted position
    if (cp.id === myId) {
      return { ...cp, x: localPlayer.x, y: localPlayer.y };
    }

    // Remote players: smooth interpolation
    const pp = prevSnapshot.players.find(p => p.id === cp.id);
    if (!pp) return { ...cp };

    let x, y;
    if (t <= 1) {
      x = lerp(pp.x, cp.x, t);
      y = lerp(pp.y, cp.y, t);
    } else {
      const extra = (t - 1) * SNAPSHOT_INTERVAL / 16.67;
      x = cp.x + (cp.vx || 0) * extra * FRICTION_PLAYER;
      y = cp.y + (cp.vy || 0) * extra * FRICTION_PLAYER;
    }
    return { ...cp, x, y };
  });
}

// ─── RENDER LOOP ─────────────────────────────────────────────
function render(timestamp) {
  requestAnimationFrame(render);
  if (!curSnapshot) return;

  const dt = timestamp - lastFrameTime;
  lastFrameTime = timestamp;

  // Run local prediction every frame
  updateLocalPlayer(dt);

  // Interpolate remote entities
  interpolateRemotes(performance.now());

  const s = canvasScale;
  ctx.clearRect(0, 0, els.canvas.width, els.canvas.height);
  ctx.save();
  ctx.translate(canvasOffX, canvasOffY);
  ctx.scale(s, s);
  drawField();
  drawBall(renderBall);
  drawPlayers(renderPlayers);
  ctx.restore();
}

// ─── DRAWING ─────────────────────────────────────────────────
function drawField() {
  const w = FIELD_W, h = FIELD_H;
  const goalTop = h / 2 - GOAL_SIZE / 2, goalBot = h / 2 + GOAL_SIZE / 2;

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
  ctx.strokeRect(WALL_THICKNESS, h / 2 - 140, 120, 280);
  ctx.strokeRect(w - WALL_THICKNESS - 120, h / 2 - 140, 120, 280);

  ctx.fillStyle = 'rgba(239,68,68,0.15)'; ctx.fillRect(-GOAL_DEPTH, goalTop, GOAL_DEPTH, GOAL_SIZE);
  ctx.strokeStyle = 'rgba(239,68,68,0.4)'; ctx.lineWidth = 2; ctx.strokeRect(-GOAL_DEPTH, goalTop, GOAL_DEPTH, GOAL_SIZE);
  ctx.fillStyle = 'rgba(59,130,246,0.15)'; ctx.fillRect(w, goalTop, GOAL_DEPTH, GOAL_SIZE);
  ctx.strokeStyle = 'rgba(59,130,246,0.4)'; ctx.strokeRect(w, goalTop, GOAL_DEPTH, GOAL_SIZE);

  ctx.strokeStyle = 'rgba(255,255,255,0.1)'; ctx.lineWidth = 1;
  for (let y = goalTop; y <= goalBot; y += 12) {
    ctx.beginPath(); ctx.moveTo(-GOAL_DEPTH, y); ctx.lineTo(0, y); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(w, y); ctx.lineTo(w + GOAL_DEPTH, y); ctx.stroke();
  }
  for (let x = -GOAL_DEPTH; x <= 0; x += 12) { ctx.beginPath(); ctx.moveTo(x, goalTop); ctx.lineTo(x, goalBot); ctx.stroke(); }
  for (let x = w; x <= w + GOAL_DEPTH; x += 12) { ctx.beginPath(); ctx.moveTo(x, goalTop); ctx.lineTo(x, goalBot); ctx.stroke(); }

  ctx.fillStyle = '#2d3748';
  ctx.fillRect(-GOAL_DEPTH, -4, w + GOAL_DEPTH * 2, WALL_THICKNESS + 4);
  ctx.fillRect(-GOAL_DEPTH, h - WALL_THICKNESS, w + GOAL_DEPTH * 2, WALL_THICKNESS + 4);
  ctx.fillRect(-GOAL_DEPTH - 4, -4, GOAL_DEPTH + WALL_THICKNESS + 4, goalTop + 4);
  ctx.fillRect(-GOAL_DEPTH - 4, goalBot, GOAL_DEPTH + WALL_THICKNESS + 4, h - goalBot + 4);
  ctx.fillRect(w - WALL_THICKNESS, -4, GOAL_DEPTH + WALL_THICKNESS + 4, goalTop + 4);
  ctx.fillRect(w - WALL_THICKNESS, goalBot, GOAL_DEPTH + WALL_THICKNESS + 4, h - goalBot + 4);

  [{ x: WALL_THICKNESS, y: goalTop }, { x: WALL_THICKNESS, y: goalBot }, { x: w - WALL_THICKNESS, y: goalTop }, { x: w - WALL_THICKNESS, y: goalBot }].forEach(p => {
    ctx.beginPath(); ctx.arc(p.x, p.y, 6, 0, Math.PI * 2);
    ctx.fillStyle = '#e2e8f0'; ctx.fill();
    ctx.strokeStyle = '#94a3b8'; ctx.lineWidth = 2; ctx.stroke();
  });
}

function drawBall(ball) {
  if (!ball) return;
  ctx.beginPath(); ctx.arc(ball.x + 2, ball.y + 3, ball.radius, 0, Math.PI * 2); ctx.fillStyle = 'rgba(0,0,0,0.3)'; ctx.fill();
  ctx.beginPath(); ctx.arc(ball.x, ball.y, ball.radius, 0, Math.PI * 2);
  const g = ctx.createRadialGradient(ball.x - 3, ball.y - 3, 1, ball.x, ball.y, ball.radius);
  g.addColorStop(0, '#ffffff'); g.addColorStop(1, '#d1d5db'); ctx.fillStyle = g; ctx.fill();
  ctx.strokeStyle = '#9ca3af'; ctx.lineWidth = 1.5; ctx.stroke();
  ctx.fillStyle = 'rgba(0,0,0,0.12)'; ctx.beginPath(); ctx.arc(ball.x, ball.y, ball.radius * 0.45, 0, Math.PI * 2); ctx.fill();
}

function drawPlayers(players) {
  if (!players) return;
  players.forEach(p => {
    if (p.team === 'spectator') return;
    const isMe = p.id === myId;
    const tc = p.team === 'red' ? '#ef4444' : '#3b82f6';
    const tl = p.team === 'red' ? '#fca5a5' : '#93c5fd';
    const td = p.team === 'red' ? '#b91c1c' : '#1d4ed8';

    ctx.beginPath(); ctx.arc(p.x + 1, p.y + 3, p.radius, 0, Math.PI * 2); ctx.fillStyle = 'rgba(0,0,0,0.25)'; ctx.fill();
    ctx.beginPath(); ctx.arc(p.x, p.y, p.radius, 0, Math.PI * 2);
    const g = ctx.createRadialGradient(p.x - 4, p.y - 4, 2, p.x, p.y, p.radius);
    g.addColorStop(0, tl); g.addColorStop(1, tc); ctx.fillStyle = g; ctx.fill();
    ctx.strokeStyle = isMe ? '#22d3ee' : td; ctx.lineWidth = isMe ? 3 : 2; ctx.stroke();

    if (isMe) {
      ctx.beginPath(); ctx.arc(p.x, p.y, p.radius + 4, 0, Math.PI * 2);
      ctx.strokeStyle = 'rgba(34,211,238,0.35)'; ctx.lineWidth = 2; ctx.stroke();
    }

    ctx.fillStyle = '#fff';
    ctx.font = `bold ${isMe ? 11 : 10}px Inter,sans-serif`;
    ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
    ctx.shadowColor = 'rgba(0,0,0,0.7)'; ctx.shadowBlur = 3;
    ctx.fillText(p.nickname, p.x, p.y - p.radius - 5);
    ctx.shadowBlur = 0;
  });
}

// ─── INPUT ───────────────────────────────────────────────────
const keyMap = { ArrowUp: 'up', w: 'up', W: 'up', ArrowDown: 'down', s: 'down', S: 'down', ArrowLeft: 'left', a: 'left', A: 'left', ArrowRight: 'right', d: 'right', D: 'right', ' ': 'kick', x: 'kick', X: 'kick' };

document.addEventListener('keydown', e => {
  if (e.target.tagName === 'INPUT') return;
  const a = keyMap[e.key]; if (a) { e.preventDefault(); keys[a] = true; sendInput(); }
});
document.addEventListener('keyup', e => {
  if (e.target.tagName === 'INPUT') return;
  const a = keyMap[e.key]; if (a) { keys[a] = false; sendInput(); }
});
function sendInput() {
  const enc = JSON.stringify(keys);
  if (enc !== lastSentInput) { lastSentInput = enc; socket.emit('playerInput', keys); }
}

// ─── SCREENS & UI ────────────────────────────────────────────
function showScreen(name) { Object.values(screens).forEach(s => s.classList.remove('active')); screens[name].classList.add('active'); if (name === 'game') resizeCanvas(); }
function escapeHtml(s) { const d = document.createElement('div'); d.textContent = s; return d.innerHTML; }

els.btnEnter.addEventListener('click', enterLobby);
els.inputNickname.addEventListener('keydown', e => { if (e.key === 'Enter') enterLobby(); });
function enterLobby() { const n = els.inputNickname.value.trim(); if (!n) { els.inputNickname.style.borderColor = '#ef4444'; return; } myNickname = n; socket.emit('setNickname', n); els.displayNickname.textContent = n; showScreen('lobby'); socket.emit('getRooms'); }

els.btnCreateRoom.addEventListener('click', () => { socket.emit('createRoom', { name: els.createName.value.trim() || 'Sala de ' + myNickname, password: els.createPassword.value.trim(), maxPlayers: parseInt(els.createMax.value) || 10 }); });
els.btnRefresh.addEventListener('click', () => socket.emit('getRooms'));

socket.on('roomList', rooms => {
  if (!rooms.length) { els.roomList.innerHTML = '<p class="room-empty">No hay salas. ¡Crea una!</p>'; return; }
  els.roomList.innerHTML = rooms.map(r => `<div class="room-item"><div class="room-item-info"><span class="room-item-name">${escapeHtml(r.name)}</span><div class="room-item-meta">${r.hasPassword ? '<span class="room-lock">🔒</span>' : ''}${r.gameRunning ? `<span class="room-playing">⚽ ${r.scoreRed}-${r.scoreBlue}</span>` : '<span>En espera</span>'}</div></div><div class="room-item-right"><span class="room-players-count">${r.playerCount}/${r.maxPlayers}</span><button class="btn-join-room" data-rid="${r.id}" data-pw="${r.hasPassword}">UNIRSE</button></div></div>`).join('');
  els.roomList.querySelectorAll('.btn-join-room').forEach(b => b.addEventListener('click', e => { e.stopPropagation(); joinRoom(b.dataset.rid, b.dataset.pw === 'true'); }));
});

function joinRoom(rid, hasPw) { if (hasPw) { pendingJoinRoomId = rid; els.modalPassword.classList.remove('hidden'); els.modalPasswordInput.value = ''; els.modalPasswordInput.focus(); } else { socket.emit('joinRoom', { roomId: rid, password: '' }); } }
els.modalCancel.addEventListener('click', () => { els.modalPassword.classList.add('hidden'); pendingJoinRoomId = null; });
els.modalJoin.addEventListener('click', () => { if (pendingJoinRoomId) { socket.emit('joinRoom', { roomId: pendingJoinRoomId, password: els.modalPasswordInput.value }); els.modalPassword.classList.add('hidden'); pendingJoinRoomId = null; } });
els.modalPasswordInput.addEventListener('keydown', e => { if (e.key === 'Enter') els.modalJoin.click(); });
socket.on('joinError', msg => alert(msg));

socket.on('connect', () => { myId = socket.id; });

socket.on('roomJoined', data => {
  currentRoomId = data.roomId; isHost = data.isHost;
  els.roomNameDisplay.textContent = data.roomName;
  els.settingMaxScore.value = data.maxScore || 5; els.settingTimeLimit.value = data.timeLimit || 180;
  gameRunning = false; prevSnapshot = null; curSnapshot = null; localPlayerActive = false;
  els.chatLog.innerHTML = ''; els.scoreRed.textContent = '0'; els.scoreBlue.textContent = '0'; els.timerDisplay.textContent = '0:00';
  updateHostUI(); updatePlayerLists(data.players); showScreen('game');
  showOverlay('Esperando jugadores...\n\nWASD / Flechas = moverse\nESPACIO / X = patear');
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
});

// ─── SERVER SNAPSHOTS (20Hz) ─────────────────────────────────
socket.on('gameState', state => {
  prevSnapshot = curSnapshot;
  curSnapshot = state;
  snapshotTime = performance.now();

  // Correct local player towards server position
  const me = state.players.find(p => p.id === myId);
  if (me) {
    if (!localPlayerActive) {
      localPlayer.x = me.x; localPlayer.y = me.y;
      localPlayer.vx = 0; localPlayer.vy = 0;
      localPlayer.radius = me.radius;
      localPlayerActive = true;
    } else {
      correctLocalPlayer(me.x, me.y);
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

socket.on('kicked', msg => { alert(msg); currentRoomId = null; gameRunning = false; curSnapshot = null; localPlayerActive = false; showScreen('lobby'); socket.emit('getRooms'); });

document.querySelectorAll('.btn-team').forEach(b => b.addEventListener('click', () => socket.emit('changeTeam', b.dataset.team)));

function updatePlayerLists(players) {
  const r = players.filter(p => p.team === 'red'), b = players.filter(p => p.team === 'blue'), s = players.filter(p => p.team === 'spectator');
  els.teamRedList.innerHTML = r.map(p => playerHTML(p)).join('');
  els.teamBlueList.innerHTML = b.map(p => playerHTML(p)).join('');
  els.teamSpecList.innerHTML = s.map(p => playerHTML(p)).join('');
  if (isHost) document.querySelectorAll('.player-kick-btn').forEach(b => b.addEventListener('click', () => socket.emit('kickPlayer', b.dataset.playerId)));
}
function playerHTML(p) {
  const host = p.isHost ? '<span class="player-host">★ HOST</span>' : '';
  const kick = (isHost && p.id !== myId) ? `<button class="player-kick-btn" data-player-id="${p.id}">✕</button>` : '';
  return `<div class="team-player"><span class="player-name">${escapeHtml(p.nickname)}${p.id === myId ? ' (tú)' : ''}</span><span>${host}${kick}</span></div>`;
}

function updateHostUI() { els.hostControls.style.display = isHost ? 'block' : 'none'; els.btnStartGame.style.display = gameRunning ? 'none' : 'block'; els.btnStopGame.style.display = gameRunning ? 'block' : 'none'; }
els.btnStartGame.addEventListener('click', () => socket.emit('startGame'));
els.btnStopGame.addEventListener('click', () => socket.emit('stopGame'));
els.btnSaveSettings.addEventListener('click', () => socket.emit('updateSettings', { maxScore: parseInt(els.settingMaxScore.value) || 5, timeLimit: parseInt(els.settingTimeLimit.value) || 0 }));
els.btnLeave.addEventListener('click', () => { socket.emit('leaveRoom'); currentRoomId = null; gameRunning = false; curSnapshot = null; localPlayerActive = false; showScreen('lobby'); socket.emit('getRooms'); });

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
