# webgpu.rs Precision Header

Replaces: `src/Hydrogen/GPU/WebGPU/Device.js` (444 lines)

## Required Exports (56 functions)

### Initialization (4)
- `is_webgpu_supported` - Check navigator.gpu exists
- `request_adapter` - async, returns GPUAdapter
- `request_device` - async, returns GPUDevice  
- `configure_canvas` - returns GPUCanvasContext

### Device Info (2)
- `get_limits` - returns GPUSupportedLimits
- `get_features` - returns Vec<String>

### Error Handling (2)
- `on_uncaptured_error` - callback registration
- `on_device_lost` - callback registration

### Canvas Operations (2)
- `get_current_texture` - returns GPUTexture
- `get_preferred_canvas_format` - returns GPUTextureFormat

### Buffer Operations (6)
- `create_buffer` - returns GPUBuffer
- `destroy_buffer` - void
- `write_buffer` - void
- `map_buffer_async` - async
- `unmap_buffer` - void
- `get_mapped_range` - returns ArrayBuffer

### Texture Operations (4)
- `create_texture` - returns GPUTexture
- `destroy_texture` - void
- `create_texture_view` - returns GPUTextureView
- `write_texture` - void

### Sampler Operations (1)
- `create_sampler` - returns GPUSampler

### Shader Operations (1)
- `create_shader_module` - returns GPUShaderModule

### Pipeline Operations (4)
- `create_render_pipeline` - returns GPURenderPipeline
- `create_compute_pipeline` - returns GPUComputePipeline
- `create_bind_group_layout` - returns GPUBindGroupLayout
- `create_pipeline_layout` - returns GPUPipelineLayout

### Bind Group Operations (1)
- `create_bind_group` - returns GPUBindGroup

### Command Encoding (6)
- `create_command_encoder` - returns GPUCommandEncoder
- `finish_command_encoder` - returns GPUCommandBuffer
- `begin_render_pass` - returns GPURenderPassEncoder
- `end_render_pass` - void
- `begin_compute_pass` - returns GPUComputePassEncoder
- `end_compute_pass` - void

### Render Pass Operations (10)
- `set_pipeline` - void
- `set_bind_group` - void
- `set_vertex_buffer` - void
- `set_index_buffer` - void
- `draw` - void
- `draw_indexed` - void
- `draw_indirect` - void
- `set_viewport` - void
- `set_scissor_rect` - void

### Queue Operations (1)
- `submit` - void

### Foreign Conversion Helpers (12)
- `to_foreign_adapter_desc`
- `to_foreign_device_desc`
- `to_foreign_canvas_config`
- `to_foreign_buffer_desc`
- `to_foreign_texture_desc`
- `to_foreign_sampler_desc`
- `to_foreign_shader_desc`
- `to_foreign_texture_dest`
- `to_foreign_data_layout`
- `to_foreign_size`
- `to_foreign_render_pass_desc`
- `from_foreign_limits`

## Build Requirements

```
RUSTFLAGS='--cfg=web_sys_unstable_apis' cargo build
```

## Dependencies (Cargo.toml already updated)

- wasm-bindgen
- web-sys with WebGPU features
- js-sys
