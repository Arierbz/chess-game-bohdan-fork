class Game {
  constructor(state) {
    this.state = state;

    // holders
    this.spawnedObjects = [];
    this.collidableObjects = [];
    this.enemies = [];
    this.projectiles = [];

    // constants
    this.TILE_SIZE = 1.0;
    this.GRID_SIZE = 11;
    this.MIN_ENEMY_TILES = 3;
    this.FIREBALL_SPEED = 6.0 * this.TILE_SIZE;
    this.FIREBALL_RANGE = 4.0 * this.TILE_SIZE;
    this.FIREBALL_RADIUS = 0.35 * this.TILE_SIZE;
    this.SPAWN_SAFETY_TIME = 0.2;
    this.SHOT_COOLDOWN = 1.5;

    // timers
    this.enemyMoveTimer = 0.0;
    this.enemySpawnTimer = 0.0;

    // difficulty
    this.ENEMY_MOVE_BASE = 1.5;
    this.ENEMY_MOVE_MIN  = 0.9;
    this.ENEMY_SPAWN_BASE = 5.0;
    this.ENEMY_SPAWN_MIN  = 2.8;
    this.SPEEDUP_STEP = 0.1;
    this.maxDifficultyLocked = false;

    // debug
    this.DEBUG_COLLIDERS = true;
    this._debugBoxes = new Map();
    this._debugUIButton = null;

    // runtime
    this.player = null;
    this.facingDir = vec3.fromValues(0, 0, 1);
    this.isGameOver = false;
    this.isPaused = false;
    this.timeAccumulator = 0;
    this.timeSinceStart = 0;
    this.lastShotAt = -Infinity;

    // prefabs
    this.fireballPrefab = null;
    this.rookPrefab = null;

    // ui
    this.cooldownBar = null;
    this.cooldownFill = null;

    this.score = 0;
    this.highScore = 0;
    this.scoreBox = null;
    this.scoreText = null;
    this.highText = null;
    this.speedRow = null;
    this.speedRowText = null;
    this.maxToggleBtn = null;
    this._lastSpeedString = "";
    this._speedDefaultColor = "#e5e7eb";

    this.gameOverOverlay = null;
    this.gameOverScoreEl = null;
    this.gameOverHighEl = null;
    this.gameOverBadgeEl = null;
    this.retryBtn = null;
    this._shownGameOver = false;

    this.pauseOverlay = null;
    this.continueBtn = null;
    this.resetBtn = null;

    // board align
    this.BOARD_EPSILON_Y = 0.02;
    this.boardTopY = 0.0;
  }

  // gets world position
  getWorldPos(object) {
    const m = object?.model?.modelMatrix;
    if (m) {
      const out = vec4.fromValues(0, 0, 0, 1);
      vec4.transformMat4(out, out, m);
      return vec3.fromValues(out[0], out[1], out[2]);
    }
    const p = object?.model?.position || vec3.fromValues(0, 0, 0);
    return vec3.fromValues(p[0], p[1], p[2]);
  }

  // gets world center
  getWorldCenter(object) {
    const m = object?.model?.modelMatrix;
    const c = object?.centroid || vec3.fromValues(0, 0, 0);
    if (m) {
      const v4 = vec4.fromValues(c[0], c[1], c[2], 1.0);
      vec4.transformMat4(v4, v4, m);
      return vec3.fromValues(v4[0], v4[1], v4[2]);
    }
    const p = this.getWorldPos(object);
    return vec3.fromValues(p[0] + c[0], p[1] + c[1], p[2] + c[2]);
  }

  // sets world center
  setWorldCenter(object, worldCenter) {
    const c = object?.centroid || vec3.fromValues(0,0,0);
    if (!object.model) object.model = { position: vec3.create(), rotation: mat4.create(), scale: vec3.fromValues(1,1,1) };
    object.model.position = vec3.fromValues(
      worldCenter[0] - c[0],
      worldCenter[1] - c[1],
      worldCenter[2] - c[2]
    );
  }

  // gets forward
  getForwardWorld() { const f = vec3.clone(this.facingDir); vec3.normalize(f, f); return f; }

  // gets fireball muzzle
  getMuzzleWorldPosition() {
    const center = this.getWorldCenter(this.player);
    const forward = this.getForwardWorld();
    const half = this.player?.collider?.half || vec3.fromValues(0.5, 0.5, 0.5);
    const absF = vec3.fromValues(Math.abs(forward[0]), Math.abs(forward[1]), Math.abs(forward[2]));
    const frontDist = (absF[0] >= absF[2]) ? half[0] : half[2];
    const extra = 0.05;
    const forwardOffset = vec3.scale(vec3.create(), forward, frontDist + extra);
    const upOffset = vec3.fromValues(0, half[1], 0);
    const muzzle = vec3.add(vec3.create(), center, forwardOffset);
    vec3.add(muzzle, muzzle, upOffset);
    return muzzle;
  }

  // world to tile
  worldToTileXZ(v) { return { ix: Math.round(v[0] / this.TILE_SIZE), iz: Math.round(v[2] / this.TILE_SIZE) }; }

  // tile to world
  tileToWorldXZ(ix, iz, y) { return vec3.fromValues(ix * this.TILE_SIZE, y, iz * this.TILE_SIZE); }

  // chebyshev distance
  chebyshevTileDistance(aix, aiz, bix, biz) { return Math.max(Math.abs(aix - bix), Math.abs(aiz - biz)); }

  // grid bounds
  gridBounds() { const h = Math.floor(this.GRID_SIZE / 2); return { min: -h, max: h }; }

  // in-bounds
  inBounds(ix, iz) { const b=this.gridBounds(); return ix>=b.min && ix<=b.max && iz>=b.min && iz<=b.max; }

  // object tile
  getTileOfObject(obj) { const c = this.getWorldCenter(obj); return this.worldToTileXZ(c); }

  // occupancy
  isOccupied(ix, iz, except = null) {
    const p = this.getTileOfObject(this.player);
    if (!except || except !== this.player) {
      if (p.ix === ix && p.iz === iz) return true;
    }
    for (const e of this.enemies) {
      if (except && e === except) continue;
      const t = this.getTileOfObject(e);
      if (t.ix === ix && t.iz === iz) return true;
    }
    return false;
  }

  // enemy move to tile
  moveEnemyToTile(enemy, ix, iz) {
    const curY = this.getWorldCenter(enemy)[1];
    const target = this.tileToWorldXZ(ix, iz, curY);
    this.setWorldCenter(enemy, target);
  }

  // add collider
  addAABBCollider(object, halfExtents) {
    object.collider = {
      type: "AABB",
      half: vec3.fromValues(halfExtents[0], halfExtents[1], halfExtents[2]),
      worldMin: vec3.create(),
      worldMax: vec3.create(),
    };
    this.collidableObjects.push(object);
  }

  // sync collider
  updateWorldAABB(object) {
    const c = object.collider; if (!c || c.type !== "AABB") return;
    const center = this.getWorldCenter(object);
    c.worldMin[0] = center[0] - c.half[0]; c.worldMax[0] = center[0] + c.half[0];
    c.worldMin[1] = center[1] - c.half[1]; c.worldMax[1] = center[1] + c.half[1];
    c.worldMin[2] = center[2] - c.half[2]; c.worldMax[2] = center[2] + c.half[2];
  }

  // aabb overlap
  aabbIntersect(a, b) {
    return (
      a.worldMin[0] <= b.worldMax[0] && a.worldMax[0] >= b.worldMin[0] &&
      a.worldMin[1] <= b.worldMax[1] && a.worldMax[1] >= b.worldMin[1] &&
      a.worldMin[2] <= b.worldMax[2] && a.worldMax[2] >= b.worldMin[2]
    );
  }

  // remove from scene
  removeFromScene(object) {
    const i1 = this.state.objects.indexOf(object); if (i1 >= 0) this.state.objects.splice(i1, 1);
    const i2 = this.collidableObjects.indexOf(object); if (i2 >= 0) this.collidableObjects.splice(i2, 1);
    const i3 = this.enemies.indexOf(object); if (i3 >= 0) this.enemies.splice(i3, 1);
    const i4 = this.projectiles.findIndex(p => p.object === object); if (i4 >= 0) this.projectiles.splice(i4, 1);
    const dbg = this._debugBoxes.get(object);
    if (dbg) {
      const di = this.state.objects.indexOf(dbg);
      if (di >= 0) this.state.objects.splice(di, 1);
      this._debugBoxes.delete(object);
    }
  }

  // create visible collider
  async createDebugBoxFor(object, kind) {
    if (!this.DEBUG_COLLIDERS || !object?.collider) return null;
    if (this._debugBoxes.has(object)) return this._debugBoxes.get(object);
    const c = object.collider;
    const center = this.getWorldCenter(object);
    const color =
      kind === "player" ? vec3.fromValues(0.1, 0.9, 0.2) :
      kind === "enemy"  ? vec3.fromValues(0.95, 0.2, 0.2) :
                          vec3.fromValues(0.95, 0.85, 0.2);
    const box = await spawnObject({
      name: `DEBUG_AABB_${object.name}`,
      type: "cube",
      material: {
        diffuse: color, ambient: vec3.fromValues(0.05, 0.05, 0.05),
        specular: vec3.fromValues(0, 0, 0), n: 1.0, alpha: 0.25
      },
      position: vec3.fromValues(center[0], center[1], center[2]),
      scale: vec3.fromValues(c.half[0]*2.0, c.half[1]*2.0, c.half[2]*2.0)
    }, this.state);
    this.ensureTransformAPI(box);
    box.debug = true;
    this._debugBoxes.set(object, box);
    return box;
  }

  // update visible collider
  updateDebugBox(object) {
    if (!this.DEBUG_COLLIDERS || !object?.collider) return;
    const box = this._debugBoxes.get(object);
    if (!box) return;
    const c = object.collider;
    const center = this.getWorldCenter(object);
    const targetScale = vec3.fromValues(c.half[0]*2.0, c.half[1]*2.0, c.half[2]*2.0);
    const curScale = box.model.scale;
    if (curScale[0] !== targetScale[0] || curScale[1] !== targetScale[1] || curScale[2] !== targetScale[2]) {
      box.model.scale[0] = targetScale[0];
      box.model.scale[1] = targetScale[1];
      box.model.scale[2] = targetScale[2];
    }
    const curPos = box.model.position;
    const dx = center[0]-curPos[0], dy=center[1]-curPos[1], dz=center[2]-curPos[2];
    if (Math.abs(dx)+Math.abs(dy)+Math.abs(dz) > 1e-6) box.translate(vec3.fromValues(dx,dy,dz));
  }

  // build cooldown ui
  createCooldownBarUI() {
    const host = document.createElement("div");
    Object.assign(host.style, {
      position: "fixed",
      top: "10px",
      left: "190px",
      width: "160px",
      height: "14px",
      borderRadius: "8px",
      background: "rgba(255,255,255,0.08)",
      border: "1px solid rgba(255,255,255,0.25)",
      overflow: "hidden",
      zIndex: "10000",
    });
    const fill = document.createElement("div");
    Object.assign(fill.style, {
      width: "0%",
      height: "100%",
      background: "linear-gradient(90deg, #b5b5b5, #ffffff)",
      transition: "width 80ms linear",
    });
    const label = document.createElement("div");
    label.textContent = "Fireball";
    Object.assign(label.style, {
      position: "absolute",
      top: "-18px",
      left: "2px",
      fontSize: "12px",
      color: "rgba(255,255,255,0.8)",
      userSelect: "none",
    });
    host.appendChild(fill);
    host.appendChild(label);
    document.body.appendChild(host);
    this.cooldownBar = host;
    this.cooldownFill = fill;
  }

  // update cooldown ui
  updateCooldownBar() {
    if (!this.cooldownFill) return;
    const t = Math.min(1, Math.max(0, (this.timeSinceStart - this.lastShotAt) / this.SHOT_COOLDOWN));
    this.cooldownFill.style.width = `${Math.round(t * 100)}%`;
    const r = 255, g = Math.round(255 * (1 - t)), b = Math.round(255 * (1 - t));
    this.cooldownFill.style.background = `linear-gradient(90deg, rgb(${g},${g},${g}), rgb(${r},${g},${b}))`;
  }

  // load highscore
  loadHighScore() { try { const v = localStorage.getItem("cc_highscore"); const n = v ? parseInt(v, 10) : 0; return Number.isFinite(n) ? n : 0; } catch { return 0; } }

  // save highscore
  saveHighScore() { try { localStorage.setItem("cc_highscore", String(this.highScore)); } catch {} }

  // build score ui
  createScoreUI() {
    const box = document.createElement("div");
    Object.assign(box.style, {
      position: "fixed",
      top: "10px",
      left: "370px",
      padding: "8px 12px",
      borderRadius: "8px",
      background: "rgba(31,41,55,0.75)",
      color: "#e5e7eb",
      border: "1px solid rgba(255,255,255,0.2)",
      fontFamily: "system-ui, sans-serif",
      fontSize: "14px",
      lineHeight: "1.2",
      zIndex: "10000",
      userSelect: "none",
      whiteSpace: "nowrap",
    });

    const scoreEl = document.createElement("div");
    const highEl = document.createElement("div");

    const speedRow = document.createElement("div");
    Object.assign(speedRow.style, { display: "flex", alignItems: "center", gap: "8px", marginTop: "6px" });

    const speedText = document.createElement("span");
    Object.assign(speedText.style, { fontSize: "12px", opacity: 0.95, color: this._speedDefaultColor });

    const maxBtn = document.createElement("button");
    maxBtn.textContent = "MAX";
    Object.assign(maxBtn.style, {
      padding: "2px 8px",
      fontSize: "11px",
      borderRadius: "999px",
      border: "1px solid rgba(255,255,255,0.25)",
      background: "rgba(55,65,81,0.8)",
      color: "#e5e7eb",
      cursor: "pointer",
      lineHeight: "1.4",
    });
    maxBtn.title = "Lock difficulty to max (I)";
    maxBtn.addEventListener("click", () => this.toggleMaxDifficulty());

    speedRow.appendChild(speedText);
    speedRow.appendChild(maxBtn);

    scoreEl.textContent = "Score: 000";
    highEl.textContent = "High:  000";

    box.appendChild(scoreEl);
    box.appendChild(highEl);
    box.appendChild(speedRow);
    document.body.appendChild(box);

    this.scoreBox = box;
    this.scoreText = scoreEl;
    this.highText = highEl;
    this.speedRow = speedRow;
    this.speedRowText = speedText;
    this.maxToggleBtn = maxBtn;

    this.highScore = this.loadHighScore();
    this.updateScoreUI();
    this.updateSpeedUI(true);
  }

  // update score ui
  updateScoreUI() {
    if (!this.scoreText || !this.highText) return;
    const fmt = (n) => n.toString().padStart(3, "0");
    this.scoreText.textContent = `Score: ${fmt(this.score)}`;
    this.highText.textContent  = `High:  ${fmt(this.highScore)}`;
  }

  // update speed ui
  updateSpeedUI(force = false) {
    if (!this.speedRowText) return;
    const m = this.getEnemyMoveInterval();
    const s = this.getEnemySpawnInterval();
    const suffix = this.maxDifficultyLocked ? " (MAX)" : "";
    const txt = `⏱ Move ${m.toFixed(1)}s • Spawn ${s.toFixed(1)}s${suffix}`;
    if (force || txt !== this._lastSpeedString) {
      this.speedRowText.textContent = txt;
      this._lastSpeedString = txt;
    }
    if (this.maxToggleBtn) {
      if (this.maxDifficultyLocked) {
        this.speedRowText.style.color = "#f7c948";
        this.maxToggleBtn.style.background = "linear-gradient(180deg, #fbbf24, #f59e0b)";
        this.maxToggleBtn.style.color = "#111827";
        this.maxToggleBtn.title = "Currently MAX. Click to return.";
      } else {
        this.speedRowText.style.color = this._speedDefaultColor;
        this.maxToggleBtn.style.background = "rgba(55,65,81,0.8)";
        this.maxToggleBtn.style.color = "#e5e7eb";
        this.maxToggleBtn.title = "Lock difficulty to max (I)";
      }
    }
  }

  // add score
  addScore(points) {
    if (!points) return;
    this.score += points;
    if (this.score > this.highScore) {
      this.highScore = this.score;
      this.saveHighScore();
    }
    this.updateScoreUI();
    this.updateSpeedUI();
  }

  // build game over ui
  createGameOverUI() {
    const overlay = document.createElement("div");
    Object.assign(overlay.style, {
      position: "fixed", inset: "0", background: "rgba(0,0,0,0.65)",
      display: "none", alignItems: "center", justifyContent: "center", zIndex: "10001",
    });

    const card = document.createElement("div");
    Object.assign(card.style, {
      minWidth: "320px", maxWidth: "480px", padding: "20px 24px", borderRadius: "12px",
      background: "rgba(17,24,39,0.95)", color: "#e5e7eb",
      border: "1px solid rgba(255,255,255,0.16)", textAlign: "center",
      fontFamily: "system-ui, sans-serif",
    });

    const title = document.createElement("div");
    title.textContent = "GAME OVER";
    Object.assign(title.style, { fontSize: "28px", fontWeight: "800", letterSpacing: "2px", marginBottom: "12px" });

    const badge = document.createElement("div");
    badge.textContent = "NEW HIGHSCORE!";
    Object.assign(badge.style, { display: "none", marginBottom: "10px", fontWeight: "800", color: "#f7c948" });

    const score = document.createElement("div");
    const high = document.createElement("div");
    Object.assign(score.style, { fontSize: "18px", margin: "6px 0" });
    Object.assign(high.style,  { fontSize: "16px", opacity: 0.9, marginBottom: "14px" });

    const retry = document.createElement("button");
    retry.textContent = "Retry";
    Object.assign(retry.style, {
      marginTop: "6px", padding: "10px 16px", borderRadius: "10px",
      border: "1px solid rgba(255,255,255,0.25)",
      background: "linear-gradient(180deg, #ef4444, #b91c1c)", color: "white",
      fontSize: "15px", fontWeight: "700", cursor: "pointer",
    });
    retry.addEventListener("click", () => window.location.reload());

    card.appendChild(title);
    card.appendChild(badge);
    card.appendChild(score);
    card.appendChild(high);
    card.appendChild(retry);
    overlay.appendChild(card);
    document.body.appendChild(overlay);

    this.gameOverOverlay = overlay;
    this.gameOverScoreEl = score;
    this.gameOverHighEl = high;
    this.gameOverBadgeEl = badge;
    this.retryBtn = retry;
  }

  // show game over ui
  showGameOverUI() {
    if (!this.gameOverOverlay) this.createGameOverUI();
    const fmt = (n) => n.toString().padStart(3, "0");
    const isNewHigh = this.score >= this.loadHighScore();
    if (isNewHigh) { this.highScore = this.score; this.saveHighScore(); }
    else { this.highScore = this.loadHighScore(); }
    this.gameOverScoreEl.textContent = `Score: ${fmt(this.score)}`;
    this.gameOverHighEl.textContent  = `Highscore: ${fmt(this.highScore)}`;
    this.gameOverBadgeEl.style.display = isNewHigh ? "block" : "none";
    this.gameOverOverlay.style.display = "flex";
  }

  // build pause ui
  createPauseUI() {
    const overlay = document.createElement("div");
    Object.assign(overlay.style, {
      position: "fixed", inset: "0", background: "rgba(0,0,0,0.55)",
      display: "none", alignItems: "center", justifyContent: "center", zIndex: "10002",
    });

    const card = document.createElement("div");
    Object.assign(card.style, {
      minWidth: "280px", padding: "18px 22px", borderRadius: "12px",
      background: "rgba(17,24,39,0.95)", color: "#e5e7eb",
      border: "1px solid rgba(255,255,255,0.16)", textAlign: "center",
      fontFamily: "system-ui, sans-serif",
    });

    const title = document.createElement("div");
    title.textContent = "PAUSED";
    Object.assign(title.style, { fontSize: "22px", fontWeight: "800", letterSpacing: "1px", marginBottom: "12px" });

    const btnRow = document.createElement("div");
    Object.assign(btnRow.style, { display: "flex", gap: "10px", justifyContent: "center" });

    const cont = document.createElement("button");
    cont.textContent = "Continue";
    Object.assign(cont.style, {
      padding: "10px 14px", borderRadius: "10px",
      border: "1px solid rgba(255,255,255,0.25)",
      background: "linear-gradient(180deg, #10b981, #059669)", color: "white",
      fontSize: "14px", fontWeight: "700", cursor: "pointer", minWidth: "110px",
    });

    const reset = document.createElement("button");
    reset.textContent = "Reset";
    Object.assign(reset.style, {
      padding: "10px 14px", borderRadius: "10px",
      border: "1px solid rgba(255,255,255,0.25)",
      background: "linear-gradient(180deg, #ef4444, #b91c1c)", color: "white",
      fontSize: "14px", fontWeight: "700", cursor: "pointer", minWidth: "110px",
    });

    btnRow.appendChild(cont);
    btnRow.appendChild(reset);
    card.appendChild(title);
    card.appendChild(btnRow);
    overlay.appendChild(card);
    document.body.appendChild(overlay);

    cont.addEventListener("click", () => this.togglePause(false));
    reset.addEventListener("click", () => window.location.reload());

    this.pauseOverlay = overlay;
    this.continueBtn = cont;
    this.resetBtn = reset;
  }

  // toggle pause
  togglePause(forceValue = null) {
    if (!this.pauseOverlay) this.createPauseUI();
    const next = forceValue === null ? !this.isPaused : !!forceValue;
    if (this.isGameOver) return;
    this.isPaused = next;
    this.pauseOverlay.style.display = this.isPaused ? "flex" : "none";
  }

  // ensure transforms
  ensureTransformAPI(obj) {
    if (!obj.model) obj.model = { position: vec3.fromValues(0,0,0), rotation: mat4.create(), scale: vec3.fromValues(1,1,1) };
    if (typeof obj.translate !== "function") {
      obj.translate = (v) => { obj.model.position[0] += v[0]; obj.model.position[1] += v[1]; obj.model.position[2] += v[2]; };
    }
    if (typeof obj.rotate !== "function") {
      obj.rotate = (axis, radians) => {
        const r = mat4.create();
        if (axis === 'x') mat4.rotateX(r, r, radians);
        else if (axis === 'y') mat4.rotateY(r, r, radians);
        else if (axis === 'z') mat4.rotateZ(r, r, radians);
        mat4.mul(obj.model.rotation, obj.model.rotation, r);
      };
    }
  }

  // clone prefab
  instantiateFromPrefab(prefab, name, worldCenter, scaleVec3) {
    const copyVec3 = (v) => vec3.fromValues(v[0], v[1], v[2]);
    const obj = {
      name,
      type: prefab.type,
      programInfo: prefab.programInfo,
      buffers: prefab.buffers,
      mesh: prefab.mesh,
      fileName: prefab.fileName,
      centroid: vec3.fromValues((prefab.centroid?.[0] ?? 0),(prefab.centroid?.[1] ?? 0),(prefab.centroid?.[2] ?? 0)),
      parent: null,
      material: {
        diffuse: copyVec3(prefab.material.diffuse),
        ambient: copyVec3(prefab.material.ambient),
        specular: copyVec3(prefab.material.specular),
        n: prefab.material.n,
        alpha: prefab.material.alpha,
      },
      model: {
        position: vec3.create(),
        rotation: mat4.clone(prefab.model.rotation),
        scale: scaleVec3 ? copyVec3(scaleVec3) : copyVec3(prefab.model.scale),
        modelMatrix: mat4.create(),
        texture: prefab.model.texture || null,
        textureNorm: prefab.model.textureNorm || null,
      },
    };
    this.setWorldCenter(obj, worldCenter);
    this.ensureTransformAPI(obj);
    addObjectToScene(this.state, obj);
    return obj;
  }

  // colour math helpers
  lerp(a, b, t) { return a + (b - a) * t; }
  mix3(a, b, t) {
    return vec3.fromValues(
      this.lerp(a[0], b[0], t),
      this.lerp(a[1], b[1], t),
      this.lerp(a[2], b[2], t)
    );
  }

  // computes yellow→orange→red gradient
  getFireGradient(t01) {
    const clamp = (x) => Math.max(0, Math.min(1, x));
    const t = clamp(t01);
    const yellow = vec3.fromValues(1.0, 0.92, 0.18);
    const orange = vec3.fromValues(1.0, 0.55, 0.12);
    const red    = vec3.fromValues(0.92, 0.12, 0.12);
    if (t < 0.5) return this.mix3(yellow, orange, t / 0.5);
    return this.mix3(orange, red, (t - 0.5) / 0.5);
  }

  // applies gradient + flicker
  updateProjectileFireColor(p) {
    const t = Math.max(0, Math.min(1, p.traveled / p.maxRange));
    const base = this.getFireGradient(t);
    const flicker = 0.85 + 0.15 * Math.sin((this.timeSinceStart + p.traveled) * 12.0);
    const diffuse = vec3.fromValues(base[0] * flicker, base[1] * flicker, base[2] * flicker);
    p.object.material.diffuse = diffuse;
    p.object.material.ambient = vec3.fromValues(diffuse[0] * 0.6, diffuse[1] * 0.6, diffuse[2] * 0.6);
    p.object.material.specular = vec3.fromValues(0.9, 0.5, 0.2);
    p.object.material.n = 24.0;
    p.object.material.alpha = 1.0;
  }

  // spawn fireball
  async spawnFireball(originWorldCenter, dir) {
    let obj;
    if (this.fireballPrefab) {
      const name = `fireball-${Date.now()}`;
      obj = this.instantiateFromPrefab(this.fireballPrefab, name, originWorldCenter, vec3.fromValues(0.42, 0.42, 0.42));
    } else {
      obj = await spawnObject({
        name: `fireball-cube-${Date.now()}`,
        type: "cube",
        material: { diffuse: vec3.fromValues(1,0.6,0.15), ambient: vec3.fromValues(0.4,0.25,0.08), n: 16, alpha: 1 },
        position: vec3.fromValues(0,0,0),
        scale: vec3.fromValues(0.34, 0.34, 0.34),
      }, this.state);
      this.ensureTransformAPI(obj);
      this.setWorldCenter(obj, originWorldCenter);
    }
    this.addAABBCollider(obj, [this.FIREBALL_RADIUS, this.FIREBALL_RADIUS, this.FIREBALL_RADIUS]);
    const projectile = { object: obj, dir: vec3.normalize(vec3.create(), dir), traveled: 0, maxRange: this.FIREBALL_RANGE };
    this.updateProjectileFireColor(projectile);
    this.projectiles.push(projectile);
    this.spawnedObjects.push(obj);
    if (this.DEBUG_COLLIDERS) await this.createDebugBoxFor(obj, "proj");
    return projectile;
  }

  // explode 3x3
  explodeAt(pos) {
    const killed = [];
    for (const enemy of [...this.enemies]) {
      const epos = this.getWorldCenter(enemy);
      const { ix: ex, iz: ez } = this.worldToTileXZ(epos);
      const { ix: cx, iz: cz } = this.worldToTileXZ(pos);
      if (this.chebyshevTileDistance(ex, ez, cx, cz) <= 1.0 + 1e-3) killed.push(enemy);
    }
    for (const e of killed) this.removeFromScene(e);
    if (killed.length > 0) this.addScore(killed.length * 100);
  }

  // clamp sign
  signClamp(v) { return v === 0 ? 0 : (v > 0 ? 1 : -1); }

  // danger tiles
  isDangerTile(ix, iz) {
    for (const p of this.projectiles) {
      const pc = this.getWorldCenter(p.object);
      const pt = this.worldToTileXZ(pc);
      if (pt.ix === ix && pt.iz === iz) return true;
      const dx = Math.round(Math.sign(p.dir[0]));
      const dz = Math.round(Math.sign(p.dir[2]));
      const next = { ix: pt.ix + dx, iz: pt.iz + dz };
      if (next.ix === ix && next.iz === iz) return true;
      if (dx !== 0 && iz === pt.iz && Math.sign(ix - pt.ix) === dx && Math.abs(ix - pt.ix) <= 2) return true;
      if (dz !== 0 && ix === pt.ix && Math.sign(iz - pt.iz) === dz && Math.abs(iz - pt.iz) <= 2) return true;
    }
    return false;
  }

  // choose enemy step
  chooseEnemyStep(enemy) {
    const eT = this.getTileOfObject(enemy);
    const pT = this.getTileOfObject(this.player);
    const baseDx = this.signClamp(pT.ix - eT.ix);
    const baseDz = this.signClamp(pT.iz - eT.iz);
    const cand = { ix: eT.ix + baseDx, iz: eT.iz + baseDz };
    const valid = (t) => this.inBounds(t.ix, t.iz) && !this.isOccupied(t.ix, t.iz, enemy);
    if (valid(cand) && !this.isDangerTile(cand.ix, cand.iz)) return cand;

    const neighbors = [];
    for (let dz = -1; dz <= 1; dz++) {
      for (let dx = -1; dx <= 1; dx++) {
        if (dx === 0 && dz === 0) continue;
        const t = { ix: eT.ix + dx, iz: eT.iz + dz };
        if (!valid(t)) continue;
        const distAfter = this.chebyshevTileDistance(t.ix, t.iz, pT.ix, pT.iz);
        const distNow   = this.chebyshevTileDistance(eT.ix, eT.iz, pT.ix, pT.iz);
        const toward = distAfter <= distNow;
        const danger = this.isDangerTile(t.ix, t.iz);
        neighbors.push({ t, toward, danger, distAfter });
      }
    }
    neighbors.sort((a,b) => {
      if (a.danger !== b.danger) return a.danger ? 1 : -1;
      if (a.toward !== b.toward) return a.toward ? -1 : 1;
      return a.distAfter - b.distAfter;
    });
    return neighbors.length ? neighbors[0].t : eT;
  }

  // speed steps
  getSpeedupSteps() { return Math.floor(this.score / 1000); }

  // move interval
  getEnemyMoveInterval() {
    if (this.maxDifficultyLocked) return this.ENEMY_MOVE_MIN;
    const steps = this.getSpeedupSteps();
    return Math.max(this.ENEMY_MOVE_MIN, this.ENEMY_MOVE_BASE - steps * this.SPEEDUP_STEP);
  }

  // spawn interval
  getEnemySpawnInterval() {
    if (this.maxDifficultyLocked) return this.ENEMY_SPAWN_MIN;
    const steps = this.getSpeedupSteps();
    return Math.max(this.ENEMY_SPAWN_MIN, this.ENEMY_SPAWN_BASE - steps * this.SPEEDUP_STEP);
  }

  // tick enemy moves
  moveEnemiesTick() {
    for (const enemy of this.enemies) {
      const next = this.chooseEnemyStep(enemy);
      const cur = this.getTileOfObject(enemy);
      if (next.ix === cur.ix && next.iz === cur.iz) continue;
      this.moveEnemyToTile(enemy, next.ix, next.iz);
    }
  }

  // pick spawn tile
  findSpawnTile() {
    const b = this.gridBounds();
    const p = this.getTileOfObject(this.player);
    const candidates = [];
    for (let iz = b.min; iz <= b.max; iz++) {
      for (let ix = b.min; ix <= b.max; ix++) {
        if (this.chebyshevTileDistance(ix, iz, p.ix, p.iz) < this.MIN_ENEMY_TILES) continue;
        if (this.isOccupied(ix, iz, null)) continue;
        candidates.push({ ix, iz });
      }
    }
    if (candidates.length === 0) return null;
    const r = Math.floor(Math.random() * candidates.length);
    return candidates[r];
  }

  // spawn enemy at tile
  async spawnEnemyAtTile(ix, iz) {
    let obj;
    const y = this.getWorldCenter(this.player)[1];
    const world = this.tileToWorldXZ(ix, iz, y);

    if (this.rookPrefab) {
      const name = `rook-${Date.now()}-${Math.floor(Math.random()*1000)}`;
      obj = this.instantiateFromPrefab(this.rookPrefab, name, world, null);
    } else {
      obj = await spawnObject({
        name: `rook-fallback-${Date.now()}`,
        type: "cube",
        material: {
          diffuse: vec3.fromValues(0.85, 0.15, 0.15),
          ambient: vec3.fromValues(0.2, 0.05, 0.05),
          specular: vec3.fromValues(0.0, 0.0, 0.0),
          n: 8.0, alpha: 1.0,
        },
        position: vec3.fromValues(world[0], world[1], world[2]),
        scale: vec3.fromValues(1, 1, 1),
      }, this.state);
      this.ensureTransformAPI(obj);
    }

    const defaultHalf = (o) => {
      const s = o?.model?.scale || vec3.fromValues(1, 1, 1);
      return [Math.max(0.45 * s[0], 0.45), Math.max(0.45 * s[1], 0.45), Math.max(0.45 * s[2], 0.45)];
    };

    this.addAABBCollider(obj, defaultHalf(obj));
    this.enemies.push(obj);

    const worldXZ = this.tileToWorldXZ(ix, iz, 0);
    const cur = this.getWorldCenter(obj);
    this.setWorldCenter(obj, vec3.fromValues(worldXZ[0], cur[1], worldXZ[2]));
    this.alignObjectToBoardTop(obj);

    if (this.DEBUG_COLLIDERS) await this.createDebugBoxFor(obj, "enemy");
  }

  // bind input
  bindControls() {
    document.addEventListener("keypress", async (e) => {
      if (this.isGameOver || this.isPaused || !this.player) return;
      e.preventDefault();
      switch (e.key) {
        case "a": this.player.translate(vec3.fromValues(+1 * this.TILE_SIZE, 0, 0)); this.facingDir = vec3.fromValues(+1, 0, 0); break;
        case "d": this.player.translate(vec3.fromValues(-1 * this.TILE_SIZE, 0, 0)); this.facingDir = vec3.fromValues(-1, 0, 0); break;
        case "w": this.player.translate(vec3.fromValues(0, 0, +1 * this.TILE_SIZE)); this.facingDir = vec3.fromValues(0, 0, +1); break;
        case "s": this.player.translate(vec3.fromValues(0, 0, -1 * this.TILE_SIZE)); this.facingDir = vec3.fromValues(0, 0, -1); break;
        case " ":
          if (this.timeSinceStart - this.lastShotAt >= this.SHOT_COOLDOWN) {
            this.lastShotAt = this.timeSinceStart;
            const muzzle = this.getMuzzleWorldPosition();
            await this.spawnFireball(muzzle, this.getForwardWorld());
          }
          break;
        case "t":
        case "T":
          await this.toggleDebugColliders();
          break;
        default: break;
      }
    }, false);

    document.addEventListener("keydown", (e) => {
      if (this.isGameOver) return;
      if (e.key === "Escape") { e.preventDefault(); this.togglePause(); return; }
      if (e.key === "i" || e.key === "I") { e.preventDefault(); this.toggleMaxDifficulty(); }
    }, false);
  }

  // move to center
  moveTo(object, worldTargetCenter) { this.setWorldCenter(object, worldTargetCenter); }

  // place player
  placePlayerAtGridCenter() { const y = this.getWorldCenter(this.player)[1]; this.moveTo(this.player, vec3.fromValues(0, y, 0)); }

  // relocate enemies
  relocateEnemiesAwayFromPlayer() {
    const bounds = this.gridBounds();
    const pPos = this.getWorldCenter(this.player);
    const { ix: px, iz: pz } = this.worldToTileXZ(pPos);
    const occ = new Set([`${px},${pz}`]);

    const findSpot = (prefIx, prefIz) => {
      let best = null, bestD2 = Infinity;
      for (let iz = bounds.min; iz <= bounds.max; iz++) {
        for (let ix = bounds.min; ix <= bounds.max; ix++) {
          if (this.chebyshevTileDistance(ix, iz, px, pz) < this.MIN_ENEMY_TILES) continue;
          if (occ.has(`${ix},${iz}`)) continue;
          const d2 = (ix - prefIx) ** 2 + (iz - prefIz) ** 2;
          if (d2 < bestD2) { bestD2 = d2; best = { ix, iz }; }
        }
      }
      return best;
    };

    for (const enemy of this.enemies) {
      const ePos = this.getWorldCenter(enemy);
      const { ix: ex, iz: ez } = this.worldToTileXZ(ePos);
      const tooClose = this.chebyshevTileDistance(ex, ez, px, pz) < this.MIN_ENEMY_TILES;
      const taken = occ.has(`${ex},${ez}`);
      const targetTile = (tooClose || taken) ? (findSpot(ex, ez) || { ix: bounds.max, iz: bounds.max }) : { ix: ex, iz: ez };
      this.moveTo(enemy, this.tileToWorldXZ(targetTile.ix, targetTile.iz, ePos[1]));
      this.alignObjectToBoardTop(enemy);
      occ.add(`${targetTile.ix},${targetTile.iz}`);
    }
  }

  // toggle colliders
  async setDebugCollidersEnabled(flag) {
    if (flag === this.DEBUG_COLLIDERS) return;
    this.DEBUG_COLLIDERS = flag;
    if (!flag) {
      for (const [, box] of this._debugBoxes) {
        const di = this.state.objects.indexOf(box);
        if (di >= 0) this.state.objects.splice(di, 1);
      }
      this._debugBoxes.clear();
      if (this._debugUIButton) this._debugUIButton.textContent = "Show Colliders (T)";
      return;
    }
    if (this.player?.collider) await this.createDebugBoxFor(this.player, "player");
    for (const e of this.enemies) if (e?.collider) await this.createDebugBoxFor(e, "enemy");
    for (const p of this.projectiles) if (p.object?.collider) await this.createDebugBoxFor(p.object, "proj");
    if (this._debugUIButton) this._debugUIButton.textContent = "Hide Colliders (T)";
  }

  // toggle colliders
  async toggleDebugColliders() { await this.setDebugCollidersEnabled(!this.DEBUG_COLLIDERS); }

  // build ui bundle
  createDebugToggleUI() {
    const btn = document.createElement("button");
    btn.textContent = this.DEBUG_COLLIDERS ? "Hide Colliders (T)" : "Show Colliders (T)";
    Object.assign(btn.style, {
      position: "fixed", top: "10px", left: "10px", padding: "8px 12px", zIndex: "9999",
      fontFamily: "sans-serif", fontSize: "14px", border: "1px solid #444", borderRadius: "8px",
      background: "#1f2937", color: "#e5e7eb", opacity: "0.85", cursor: "pointer"
    });
    btn.onmouseenter = () => (btn.style.opacity = "1");
    btn.onmouseleave = () => (btn.style.opacity = "0.85");
    btn.addEventListener("click", () => this.toggleDebugColliders());
    document.body.appendChild(btn);
    this._debugUIButton = btn;

    this.createCooldownBarUI();
    this.createScoreUI();
    this.createGameOverUI();
    this.createPauseUI();
  }

  // detect board top
  detectBoardTopY() {
    const board = getObject(this.state, "board2");
    if (board && board.model) {
      const center = this.getWorldCenter(board);
      const sy = board.model.scale ? board.model.scale[1] : 1.0;
      return center[1] + sy * 0.5;
    }
    const plat = getObject(this.state, "platform");
    if (plat) {
      const pc = this.getWorldCenter(plat);
      return pc[1];
    }
    return 0.0;
  }

  // align object to board
  alignObjectToBoardTop(object) {
    if (!object) return;
    const halfY = object?.collider?.half?.[1] ?? (object?.model?.scale ? object.model.scale[1] * 0.5 : 0.5);
    const cur = this.getWorldCenter(object);
    const targetY = this.boardTopY + halfY + this.BOARD_EPSILON_Y;
    if (Math.abs(cur[1] - targetY) < 1e-6) return;
    const next = vec3.fromValues(cur[0], targetY, cur[2]);
    this.setWorldCenter(object, next);
  }

  // set max difficulty
  setMaxDifficultyLocked(flag) {
    this.maxDifficultyLocked = !!flag;
    this.enemyMoveTimer = 0.0;
    this.enemySpawnTimer = 0.0;
    this.updateSpeedUI(true);
  }

  // toggle max difficulty
  toggleMaxDifficulty() { this.setMaxDifficultyLocked(!this.maxDifficultyLocked); }

  // custom hook
  customMethod() { console.log("Custom method!"); }

  // init
  async onStart() {
    const objs = this.state.objects || [];
    this.player = getObject(this.state, "pawn") || objs.find(o => (o.name || "").toLowerCase() === "pawn");
    if (!this.player) throw new Error("Player (pawn) not found in scene.");
    this.enemies = objs.filter(o => (o.name || "").toLowerCase().startsWith("rook"));

    this.fireballPrefab = getObject(this.state, "fireball") || null;
    if (this.fireballPrefab?.model) {
      this.fireballPrefab.material.alpha = 0.0;
      this.fireballPrefab.model.scale = vec3.fromValues(0.0001, 0.0001, 0.0001);
      this.fireballPrefab.model.position = vec3.fromValues(9999, -9999, 9999);
      this.ensureTransformAPI(this.fireballPrefab);
    }
    this.rookPrefab = getObject(this.state, "rook") || null;
    if (this.rookPrefab?.model) this.ensureTransformAPI(this.rookPrefab);

    const defaultHalf = (o) => {
      const s = o?.model?.scale || vec3.fromValues(1, 1, 1);
      return [Math.max(0.45 * s[0], 0.45), Math.max(0.45 * s[1], 0.45), Math.max(0.45 * s[2], 0.45)];
    };
    this.addAABBCollider(this.player, defaultHalf(this.player));
    for (const e of this.enemies) this.addAABBCollider(e, defaultHalf(e));

    this.boardTopY = this.detectBoardTopY();

    this.placePlayerAtGridCenter();
    this.alignObjectToBoardTop(this.player);

    this.relocateEnemiesAwayFromPlayer();
    for (const e of this.enemies) this.alignObjectToBoardTop(e);

    if (this.DEBUG_COLLIDERS) {
      await this.createDebugBoxFor(this.player, "player");
      for (const e of this.enemies) await this.createDebugBoxFor(e, "enemy");
    }

    this.ensureTransformAPI(this.player);
    for (const e of this.enemies) this.ensureTransformAPI(e);

    this.createDebugToggleUI();
    this.bindControls();
    this.customMethod();

    this.score = 0;
    this.highScore = this.loadHighScore();
    this.updateScoreUI();
    this.updateSpeedUI(true);
  }

  // per-frame update
  onUpdate(deltaTime) {
    if (this.isGameOver) return;

    if (this.isPaused) {
      this.updateCooldownBar();
      this.updateSpeedUI();
      return;
    }

    this.timeAccumulator += deltaTime;
    this.timeSinceStart += deltaTime;

    if (this.player?.collider) this.updateWorldAABB(this.player);
    for (const e of this.enemies) this.updateWorldAABB(e);
    for (const p of this.projectiles) this.updateWorldAABB(p.object);

    if (this.DEBUG_COLLIDERS) {
      this.updateDebugBox(this.player);
      for (const e of this.enemies) this.updateDebugBox(e);
      for (const p of this.projectiles) this.updateDebugBox(p.object);
    }

    this.updateCooldownBar();
    this.updateSpeedUI();

    this.enemyMoveTimer += deltaTime;
    const moveInterval = this.getEnemyMoveInterval();
    while (this.enemyMoveTimer >= moveInterval) {
      this.enemyMoveTimer -= moveInterval;
      this.moveEnemiesTick();
    }

    this.enemySpawnTimer += deltaTime;
    const spawnInterval = this.getEnemySpawnInterval();
    while (this.enemySpawnTimer >= spawnInterval) {
      this.enemySpawnTimer -= spawnInterval;
      const tile = this.findSpawnTile();
      if (tile) this.spawnEnemyAtTile(tile.ix, tile.iz);
    }

    if (this.timeSinceStart > this.SPAWN_SAFETY_TIME) {
      const playerPos = this.getWorldCenter(this.player);
      const { ix: px, iz: pz } = this.worldToTileXZ(playerPos);
      const danger = this.enemies.some(e => {
        const { ix, iz } = this.worldToTileXZ(this.getWorldCenter(e));
        return this.chebyshevTileDistance(ix, iz, px, pz) <= 1.0 + 1e-3;
      });
      if (danger) {
        this.isGameOver = true;
        if (!this._shownGameOver) { this._shownGameOver = true; this.showGameOverUI(); }
        return;
      }
    }

    for (let i = this.projectiles.length - 1; i >= 0; --i) {
      const p = this.projectiles[i];
      const step = this.FIREBALL_SPEED * deltaTime;
      p.object.translate(vec3.scale(vec3.create(), p.dir, step));
      p.traveled += step;
      this.updateWorldAABB(p.object);
      this.updateProjectileFireColor(p);

      let hit = false;
      for (const e of this.enemies) {
        if (this.aabbIntersect(p.object.collider, e.collider)) { hit = true; break; }
      }
      if (hit || p.traveled >= p.maxRange) {
        const impact = this.getWorldCenter(p.object);
        this.explodeAt(impact);
        this.removeFromScene(p.object);
      }
    }
  }
}
