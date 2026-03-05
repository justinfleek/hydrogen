// FFI for Hydrogen.GPU.WebGPU.Device
// WebGPU API bindings

// Check WebGPU support
export const isWebGPUSupportedImpl = () => 'gpu' in navigator;

// Request adapter
export const requestAdapterImpl = options => onSuccess => onError => () => {
  if (!navigator.gpu) {
    onError("WebGPU not supported")();
    return;
  }
  navigator.gpu.requestAdapter(options).then(
    adapter => {
      if (adapter) {
        onSuccess(adapter)();
      } else {
        onError("Failed to get WebGPU adapter")();
      }
    },
    err => onError(err.message || "Adapter request failed")()
  );
};

// Request device
export const requestDeviceImpl = adapter => options => onSuccess => onError => () => {
  adapter.requestDevice(options).then(
    device => onSuccess(device)(),
    err => onError(err.message || "Device request failed")()
  );
};

// Configure canvas
export const configureCanvasImpl = context => config => () => {
  context.configure(config);
};

// Get queue
export const getQueueImpl = device => () => device.queue;

// Get limits
export const getLimitsImpl = device => () => device.limits;

// Get features
export const getFeaturesImpl = device => () => Array.from(device.features);

// Error handlers
export const onUncapturedErrorImpl = device => callback => () => {
  device.addEventListener('uncapturederror', e => callback(e.error)());
};

export const onDeviceLostImpl = device => callback => () => {
  device.lost.then(info => callback(info.message)());
};

// Canvas context
export const getCurrentTextureImpl = context => () => context.getCurrentTexture();

export const getPreferredCanvasFormatImpl = () => navigator.gpu.getPreferredCanvasFormat();

// Buffer operations
export const createBufferImpl = device => desc => () => device.createBuffer(desc);

export const destroyBufferImpl = buffer => () => buffer.destroy();

export const writeBufferImpl = queue => buffer => offset => data => dataOffset => size => () => {
  queue.writeBuffer(buffer, offset, data, dataOffset, size);
};

export const mapBufferAsyncImpl = buffer => mode => onSuccess => onError => () => {
  buffer.mapAsync(mode).then(
    () => onSuccess()(),
    err => onError(err.message || "Map failed")()
  );
};

export const unmapBufferImpl = buffer => () => buffer.unmap();

export const getMappedRangeImpl = buffer => offset => size => () => buffer.getMappedRange(offset, size);

// Texture operations
export const createTextureImpl = device => desc => () => device.createTexture(desc);

export const destroyTextureImpl = texture => () => texture.destroy();

export const createTextureViewImpl = texture => desc => () => 
  desc ? texture.createView(desc) : texture.createView();

export const writeTextureImpl = queue => dest => data => layout => size => () => {
  queue.writeTexture(dest, data, layout, size);
};

// Sampler
export const createSamplerImpl = device => desc => () => device.createSampler(desc);

// Shader
export const createShaderModuleImpl = device => desc => () => device.createShaderModule(desc);

// Pipelines
export const createRenderPipelineImpl = device => desc => () => device.createRenderPipeline(desc);

export const createComputePipelineImpl = device => desc => () => device.createComputePipeline(desc);

// Bind groups
export const createBindGroupLayoutImpl = device => desc => () => device.createBindGroupLayout(desc);

export const createPipelineLayoutImpl = device => desc => () => device.createPipelineLayout(desc);

export const createBindGroupImpl = device => desc => () => device.createBindGroup(desc);

// Command encoding
export const createCommandEncoderImpl = device => () => device.createCommandEncoder();

export const finishCommandEncoderImpl = encoder => () => encoder.finish();

export const beginRenderPassImpl = encoder => desc => () => encoder.beginRenderPass(desc);

export const endRenderPassImpl = pass => () => pass.end();

export const beginComputePassImpl = encoder => () => encoder.beginComputePass();

export const endComputePassImpl = pass => () => pass.end();

// Render pass commands
export const setPipelineImpl = pass => pipeline => () => pass.setPipeline(pipeline);

export const setBindGroupImpl = pass => index => group => () => pass.setBindGroup(index, group);

export const setVertexBufferImpl = pass => slot => buffer => offset => size => () => {
  pass.setVertexBuffer(slot, buffer, offset, size);
};

export const setIndexBufferImpl = pass => buffer => format => offset => size => () => {
  pass.setIndexBuffer(buffer, format, offset, size);
};

export const drawImpl = pass => vertexCount => instanceCount => firstVertex => firstInstance => () => {
  pass.draw(vertexCount, instanceCount, firstVertex, firstInstance);
};

export const drawIndexedImpl = pass => indexCount => instanceCount => firstIndex => baseVertex => firstInstance => () => {
  pass.drawIndexed(indexCount, instanceCount, firstIndex, baseVertex, firstInstance);
};

export const drawIndirectImpl = pass => buffer => offset => () => {
  pass.drawIndirect(buffer, offset);
};

export const setViewportImpl = pass => x => y => w => h => minDepth => maxDepth => () => {
  pass.setViewport(x, y, w, h, minDepth, maxDepth);
};

export const setScissorRectImpl = pass => x => y => w => h => () => {
  pass.setScissorRect(x, y, w, h);
};

// Queue submit
export const submitImpl = queue => commands => () => queue.submit(commands);

// Foreign conversion helpers
export const toForeignAdapterDesc = desc => desc;
export const toForeignDeviceDesc = desc => desc;
export const toForeignCanvasConfig = config => config;
export const toForeignBufferDesc = desc => desc;
export const toForeignTextureDesc = desc => desc;
export const toForeignSamplerDesc = desc => desc;
export const toForeignShaderDesc = desc => desc;
export const toForeignTextureDest = texture => ({ texture });
export const toForeignDataLayout = layout => ({ bytesPerRow: layout.width * 4, rowsPerImage: layout.height });
export const toForeignSize = size => size;
export const toForeignRenderPassDesc = desc => view => depthView => ({
  colorAttachments: [{
    view: view,
    loadOp: desc.colorLoadOp || 'clear',
    storeOp: desc.colorStoreOp || 'store',
    clearValue: desc.clearColor || { r: 0, g: 0, b: 0, a: 1 }
  }],
  depthStencilAttachment: depthView ? {
    view: depthView,
    depthLoadOp: desc.depthLoadOp || 'clear',
    depthStoreOp: desc.depthStoreOp || 'store',
    depthClearValue: desc.depthClearValue || 1.0
  } : undefined
});

export const fromForeignLimits = limits => limits;
