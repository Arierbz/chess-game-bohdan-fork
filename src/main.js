var state = {};
var game;
var sceneFile = "scene.json";

window.onload = async () => {
  try {
    console.log("Starting to load scene file");
    await parseSceneFile(`./statefiles/${sceneFile}`, state);
    main();
  } catch (err) {
    console.error(err);
    alert(err);
  }
};

async function createMesh(mesh, object, vertShader, fragShader) {
  let testModel = new Model(state.gl, object, mesh);
  testModel.vertShader = vertShader ? vertShader : state.vertShaderSample;
  testModel.fragShader = fragShader ? fragShader : state.fragShaderSample;
  await testModel.setup();
  addObjectToScene(state, testModel);
  return testModel;
}

async function main() {
  const canvas = document.querySelector("#glCanvas");
  canvas.width = window.innerWidth;
  canvas.height = window.innerHeight;

  var gl = canvas.getContext("webgl2");
  if (gl === null) {
    printError('WebGL 2 not supported by your browser',
      'Check to see you are using a <a href="https://developer.mozilla.org/en-US/docs/Web/API/WebGL_API#WebGL_2_2" class="alert-link">modern browser</a>.');
    return;
  }

  const vertShaderSample =
`#version 300 es
in vec3 aPosition;
in vec3 aNormal;
in vec2 aUV;

uniform mat4 uProjectionMatrix;
uniform mat4 uViewMatrix;
uniform mat4 uModelMatrix;
uniform mat4 uNormalMatrix;
uniform vec3 uCameraPosition;

out vec3 oNormal;
out vec3 oFragPosition;
out vec3 oCameraPosition;
out vec2 oUV;

void main() {
  gl_Position = uProjectionMatrix * uViewMatrix * uModelMatrix * vec4(aPosition, 1.0);
  oFragPosition = (uModelMatrix * vec4(aPosition, 1.0)).xyz;
  oCameraPosition = uCameraPosition;
  oNormal = vec3((uNormalMatrix * vec4(aNormal, 0.0)).xyz);
  oUV = aUV;
}
`;

  const fragShaderSample =
`#version 300 es
#define MAX_LIGHTS 20
precision highp float;

in vec3 oNormal;
in vec3 oFragPosition;
in vec3 oCameraPosition;
in vec2 oUV;

uniform vec3 diffuseVal;
uniform vec3 ambientVal;
uniform vec3 specularVal;
uniform float nVal;
uniform float alpha;

uniform int numLights;
uniform vec3 uLightPositions[MAX_LIGHTS];
uniform vec3 uLightColours[MAX_LIGHTS];
uniform float uLightStrengths[MAX_LIGHTS];

uniform sampler2D uTexture;
uniform int samplerExists;

out vec4 fragColor;

void main() {
  vec3 N = normalize(oNormal);
  vec3 V = normalize(oCameraPosition - oFragPosition);
  vec3 totalColour = vec3(0.0);

  int loopNumber = numLights > MAX_LIGHTS ? MAX_LIGHTS : numLights;
  for (int i = 0; i < loopNumber; i++) {
    vec3 lightPos = uLightPositions[i];
    vec3 lightColour = uLightColours[i];
    float lightStrength = uLightStrengths[i];

    vec3 L = normalize(lightPos - oFragPosition);

    vec3 ambient = ambientVal * lightColour * lightStrength;

    vec3 H = normalize(V + L);
    float spec = pow(max(dot(H, N), 0.0), nVal);
    vec3 specular = spec * specularVal * lightColour * lightStrength;

    float diff = max(dot(L, N), 0.0);
    vec3 diffusecolor = (samplerExists == 1) ? texture(uTexture, oUV).rgb : diffuseVal;
    vec3 diffuse = diff * diffusecolor * lightColour * lightStrength;

    totalColour += ambient + diffuse + specular;
  }
  fragColor = vec4(totalColour, alpha);
}
`;

  state = {
    ...state,
    gl,
    vertShaderSample,
    fragShaderSample,
    canvas: canvas,
    objectCount: 0,
    lightIndices: [],
    keyboard: {},
    mouse: { sensitivity: 0.2 },
    meshCache: {},
    samplerExists: 0,
    samplerNormExists: 0,
  };

  state.numLights = state.pointLights.length;

  const now = new Date();
  for (let i = 0; i < state.loadObjects.length; i++) {
    const object = state.loadObjects[i];

    if (object.type === "mesh") {
      await addMesh(object);
    } else if (object.type === "cube") {
      addCube(object, state);
    } else if (object.type === "plane") {
      addPlane(object, state);
    } else if (object.type.includes("Custom")) {
      addCustom(object, state);
    }
    console.log(`loaded ${object.name};`);
  }

  const then = new Date();
  const loadingTime = (then.getTime() - now.getTime()) / 1000;
  console.log(`Scene file loaded in ${loadingTime} seconds.`);

  game = new Game(state);
  await game.onStart();
  loadingPage.remove();
  startRendering(gl, state);
}

function addObjectToScene(state, object) {
  object.name = object.name;
  state.objects.push(object);
}

function startRendering(gl, state) {
  var then = 0.0;

  function render(now) {
    now *= 0.001;
    const deltaTime = now - then;
    then = now;

    state.deltaTime = deltaTime;
    drawScene(gl, deltaTime, state);
    game.onUpdate(deltaTime);

    requestAnimationFrame(render);
  }

  requestAnimationFrame(render);
}

// --------- RENDER WITH HUD PASS-THROUGH & SAFE SORT ---------
function drawScene(gl, deltaTime, state) {
  gl.clearColor(state.settings.backgroundColor[0], state.settings.backgroundColor[1], state.settings.backgroundColor[2], 1.0);
  gl.enable(gl.DEPTH_TEST);
  gl.depthFunc(gl.LEQUAL);
  gl.disable(gl.CULL_FACE);
  gl.cullFace(gl.BACK);
  gl.clearDepth(1.0);
  gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);

  const nonHud = state.objects.filter(o => !o.isHUD);
  const hud    = state.objects.filter(o =>  o.isHUD);

  const opaqueWorld = [];
  const transparentWorld = [];

  for (const o of nonHud) {
    if (o.material && o.material.alpha < 1.0) {
      transparentWorld.push(o);
    } else {
      opaqueWorld.push(o);
    }
  }

  // Helper: robust world-centroid (tolerates missing centroid/modelMatrix)
  const worldCentroid = (o) => {
    const c = o?.centroid || [0, 0, 0];
    const m = o?.model?.modelMatrix;
    if (m) {
      const v4 = vec4.fromValues(c[0] || 0, c[1] || 0, c[2] || 0, 1.0);
      vec4.transformMat4(v4, v4, m);
      return vec3.fromValues(v4[0], v4[1], v4[2]);
    }
    const p = o?.model?.position || [0, 0, 0];
    return vec3.fromValues((p[0] || 0) + (c[0] || 0), (p[1] || 0) + (c[1] || 0), (p[2] || 0) + (c[2] || 0));
  };

  // Safe sort by distance to camera
  const cam = state.camera.position;
  nonHud.sort((a, b) => {
    const aw = worldCentroid(a);
    const bw = worldCentroid(b);
    const da = vec3.distance(cam, aw);
    const db = vec3.distance(cam, bw);
    return da >= db ? -1 : 1;
  });

  const renderList = (list) => {
    list.map((object) => {
      gl.useProgram(object.programInfo.program);
      {
        // Projection
        let projectionMatrix = mat4.create();
        let fovy = 90.0 * Math.PI / 180.0;
        let aspect = state.canvas.clientWidth / state.canvas.clientHeight;
        let near = 0.1, far = 1000000.0;
        mat4.perspective(projectionMatrix, fovy, aspect, near, far);
        gl.uniformMatrix4fv(object.programInfo.uniformLocations.projection, false, projectionMatrix);
        state.projectionMatrix = projectionMatrix;

        // View
        let viewMatrix = mat4.create();
        let camFront = vec3.fromValues(0, 0, 0);
        vec3.add(camFront, state.camera.position, state.camera.front);
        mat4.lookAt(viewMatrix, state.camera.position, camFront, state.camera.up);
        gl.uniformMatrix4fv(object.programInfo.uniformLocations.view, false, viewMatrix);
        gl.uniform3fv(object.programInfo.uniformLocations.cameraPosition, state.camera.position);
        state.viewMatrix = viewMatrix;

        // Model
        let modelMatrix = mat4.create();
        let negCentroid = vec3.fromValues(0.0, 0.0, 0.0);
        const centroid = object.centroid || vec3.fromValues(0,0,0);
        vec3.negate(negCentroid, centroid);
        mat4.translate(modelMatrix, modelMatrix, object.model.position);
        mat4.translate(modelMatrix, modelMatrix, centroid);
        mat4.mul(modelMatrix, modelMatrix, object.model.rotation);
        mat4.scale(modelMatrix, modelMatrix, object.model.scale);
        mat4.translate(modelMatrix, modelMatrix, negCentroid);

        if (object.parent) {
          let parent = getObject(state, object.parent);
          if (parent.model && parent.model.modelMatrix) {
            mat4.multiply(modelMatrix, parent.model.modelMatrix, modelMatrix);
          }
        }

        object.model.modelMatrix = modelMatrix;
        gl.uniformMatrix4fv(object.programInfo.uniformLocations.model, false, modelMatrix);

        // Normal
        let normalMatrix = mat4.create();
        mat4.invert(normalMatrix, modelMatrix);
        mat4.transpose(normalMatrix, normalMatrix);
        gl.uniformMatrix4fv(object.programInfo.uniformLocations.normalMatrix, false, normalMatrix);

        // Material
        gl.uniform3fv(object.programInfo.uniformLocations.diffuseVal, object.material.diffuse);
        gl.uniform3fv(object.programInfo.uniformLocations.ambientVal, object.material.ambient);
        gl.uniform3fv(object.programInfo.uniformLocations.specularVal, object.material.specular);
        gl.uniform1f(object.programInfo.uniformLocations.nVal, object.material.n);
        gl.uniform1f(object.programInfo.uniformLocations.alpha, object.material.alpha);

        // Lights
        gl.uniform1i(object.programInfo.uniformLocations.numLights, state.numLights);
        if (state.pointLights.length > 0) {
          const numLights = state.pointLights.length;
          const lightPositions = new Float32Array(numLights * 3);
          const lightColours   = new Float32Array(numLights * 3);
          const lightStrengths = new Float32Array(numLights);
          for (let i = 0; i < numLights; i++) {
            const light = state.pointLights[i];
            lightPositions[i*3+0] = light.position[0];
            lightPositions[i*3+1] = light.position[1];
            lightPositions[i*3+2] = light.position[2];
            lightColours[i*3+0] = light.colour[0];
            lightColours[i*3+1] = light.colour[1];
            lightColours[i*3+2] = light.colour[2];
            lightStrengths[i] = light.strength;
          }
          gl.uniform1i(object.programInfo.uniformLocations.numLights, numLights);
          gl.uniform3fv(object.programInfo.uniformLocations.lightPositions, lightPositions);
          gl.uniform3fv(object.programInfo.uniformLocations.lightColours, lightColours);
          gl.uniform1fv(object.programInfo.uniformLocations.lightStrengths, lightStrengths);
        }

        // VAO + textures
        gl.bindVertexArray(object.buffers.vao);
        if (object.model.texture != null) {
          state.samplerExists = 1;
          gl.activeTexture(gl.TEXTURE0);
          gl.uniform1i(object.programInfo.uniformLocations.samplerExists, state.samplerExists);
          gl.uniform1i(object.programInfo.uniformLocations.sampler, 0);
          gl.bindTexture(gl.TEXTURE_2D, object.model.texture);
        } else {
          gl.activeTexture(gl.TEXTURE0);
          state.samplerExists = 0;
          gl.uniform1i(object.programInfo.uniformLocations.samplerExists, state.samplerExists);
        }

        if (object.model.textureNorm != null) {
          state.samplerNormExists = 1;
          gl.activeTexture(gl.TEXTURE1);
          gl.uniform1i(object.programInfo.uniformLocations.normalSamplerExists, state.samplerNormExists);
          gl.uniform1i(object.programInfo.uniformLocations.normalSampler, 1);
          gl.bindTexture(gl.TEXTURE_2D, object.model.textureNorm);
        } else {
          gl.activeTexture(gl.TEXTURE1);
          state.samplerNormExists = 0;
          gl.uniform1i(object.programInfo.uniformLocations.normalSamplerExists, state.samplerNormExists);
        }

        // Draw
        const offset = 0;
        if (object.type === "mesh" || object.type === "meshCustom") {
          gl.drawArrays(gl.TRIANGLES, offset, object.buffers.numVertices / 3);
        } else {
          gl.drawElements(gl.TRIANGLES, object.buffers.numVertices, gl.UNSIGNED_SHORT, offset);
        }
      }
    });
  };

  // PASS 1: world
  gl.enable(gl.DEPTH_TEST);
  gl.depthMask(true);
  gl.disable(gl.BLEND);
  renderList(opaqueWorld);

  // PASS 2: transparent world
  gl.enable(gl.DEPTH_TEST);
  gl.depthMask(false);
  gl.enable(gl.BLEND);
  gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
  renderList(transparentWorld);
  gl.disable(gl.BLEND);
  gl.depthMask(true);


  // PASS 3: HUD
  gl.disable(gl.DEPTH_TEST);
  gl.depthMask(false);
  gl.enable(gl.BLEND);
  gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
  renderList(hud);
  gl.disable(gl.BLEND);
  gl.depthMask(true);
  gl.enable(gl.DEPTH_TEST);
}