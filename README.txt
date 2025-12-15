CMPT 370 – Group 8
Chess-Shooter
Readme

========================================
Controls

W / A / S / D -> move one tile on the grid
1 -> shoot fireball (has a short cooldown)
Space -> toggle First-Person / Third-Person
Esc -> pause / resume (shows Pause overlay)
I -> lock/unlock “MAX” difficulty (for testing)
T -> show/hide collider debug boxes
Mouse Move -> look around (both views; clamped in 3rd-person)

Notes:

Killing enemies gives points.

Coins sometimes drop on enemy death. Picking a coin gives +25 points and instantly refills the fireball cooldown.

========================================
Description of folders / files

/lib -> 3rd-party libraries we use (e.g., gl-matrix, OBJ/loader, etc.)
/assets -> all textures & .obj files required for the game
/src -> source code
/statefiles -> scene data (default file name: scene.json)
/index.html -> main HTML page we render
/favicon.ico -> browser tab icon
/loading.gif -> image shown while the page loads (optional)

In /src
/commonFunctions.js -> shared helpers (rendering, buffers, shader creation, loading, etc.)
/main.js -> bootstraps WebGL, loads scene, starts Game and render loop
/game.js -> game logic (init, timers, enemy AI/pathing, coins, scoring, SFX, input)
/sceneFunctions.js -> helpers for scene manipulation (getObject, addObjectToScene, spawnObject, etc.)
/uiSetup.js -> small UI helpers (error display, etc.)

In /src/objects
/Cube.js -> cube class for rendering cubes with predefined data(was given as an example)
/Model.js -> model class for rendering 3D meshes (OBJ-backed)
/Plane.js -> plane class for rendering planes(was given as an example)
/CustomObject.js -> custom class for ad-hoc geometry (verts/norms/uvs/index buffers)

========================================
How to run it

Important: run from an HTTP server (WebGL + fetch will fail from file://).

Option A – Python livereload (recommended by professor)

pip install livereload

python server.py

This starts a dev server (by default on port 8000) and opens your browser.

If your server uses a different port, adjust URLs accordingly.

Option B – Simple Python HTTP server

From the project root:
python -m http.server 8000

Open:
http://127.0.0.1:8000

Option C – VS Code Live Server

Install the “Live Server” extension.

Right-click index.html -> “Open with Live Server”.

========================================
Scene file

The loader expects /statefiles/scene.json by default.

To use a different file name, change sceneFile at the top of /src/main.js or adjust the path in parseSceneFile(...).

========================================
Assets

All textures and .obj models must be placed in /assets and referenced by file name in scene.json.

Example: if the scene lists "fileName": "rookC.obj", the game will request /assets/rookC.obj.

If you rename an asset, update scene.json to match.

========================================
Gameplay overview (quick)

Grid: an 11x11 area centered on the board.

Player: moves one tile per key press.

Fireball: travels forward, explodes, damages a 3x3 area, then despawns; short cooldown shown in the HUD bar.

Enemies (rooks): spawn on valid tiles away from the player, step toward the player using Chebyshev distance, and try to avoid obvious fireball paths.

Coins: sometimes drop on enemy death; they float/rotate for a short time, then vanish. Collecting a coin gives +25 points and instantly refills the fireball cooldown.

Scoring: +100 per enemy kill, +25 per coin. High score is saved via localStorage.

Difficulty: enemy movement and spawn timers speed up with score; “MAX” toggle (I) locks the hardest settings.

========================================
Credits

Engine scaffolding inspired by course assignments and in-class code.

Models created in Blender (low-poly for performance).

Libraries: gl-matrix, OBJ loader (see /lib).

All other logic, UI, SFX synthesis, and gameplay by Group 8.