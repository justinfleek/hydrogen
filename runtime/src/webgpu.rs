//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                // hydrogen // runtime // webgpu
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Raw WebGPU API bindings. Replaces Device.js with pure Rust.
//!
//! Target: Electron (Chromium) - WebGPU always available.
//!
//! NOTE: The main renderer uses wgpu crate (renderer.rs).
//! This module provides low-level access when needed.

use js_sys::{Array, Object, Reflect};
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{
    Gpu, GpuAdapter, GpuBuffer, GpuCanvasContext, GpuCommandBuffer, GpuCommandEncoder,
    GpuComputePassEncoder, GpuComputePipeline, GpuDevice, GpuDeviceLostInfo, GpuPipelineLayout,
    GpuQueue, GpuRenderPassEncoder, GpuRenderPipeline, GpuSampler, GpuShaderModule,
    GpuSupportedFeatures, GpuSupportedLimits, GpuTexture, GpuTextureView, HtmlCanvasElement,
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // support detection
// ═══════════════════════════════════════════════════════════════════════════════

/// Check if WebGPU is supported.
#[wasm_bindgen]
pub fn is_webgpu_supported() -> bool {
    get_gpu().is_some()
}

/// Get the GPU object from navigator.
fn get_gpu() -> Option<Gpu> {
    let window = web_sys::window()?;
    let navigator = window.navigator();
    let gpu_val = Reflect::get(&navigator, &"gpu".into()).ok()?;
    if gpu_val.is_undefined() || gpu_val.is_null() {
        None
    } else {
        gpu_val.dyn_into::<Gpu>().ok()
    }
}

/// Request a GPU adapter.
/// Returns a Promise that resolves to GpuAdapter or rejects with error string.
#[wasm_bindgen]
pub fn request_adapter(power_preference: Option<String>) -> JsValue {
    let gpu = match get_gpu() {
        Some(g) => g,
        None => {
            return js_sys::Promise::reject(&JsValue::from_str("WebGPU not supported")).into();
        }
    };

    let options = web_sys::GpuRequestAdapterOptions::new();
    if let Some(pref) = power_preference {
        if pref == "low-power" {
            options.set_power_preference(web_sys::GpuPowerPreference::LowPower);
        } else if pref == "high-performance" {
            options.set_power_preference(web_sys::GpuPowerPreference::HighPerformance);
        }
    }

    gpu.request_adapter_with_options(&options).into()
}

/// Request a GPU device from an adapter.
/// Returns a Promise that resolves to GpuDevice.
#[wasm_bindgen]
pub fn request_device(adapter: &GpuAdapter) -> JsValue {
    adapter.request_device().into()
}

/// Configure a canvas for WebGPU rendering.
/// Returns the GPUCanvasContext.
#[wasm_bindgen]
pub fn configure_canvas(
    device: &GpuDevice,
    canvas: &HtmlCanvasElement,
    format: &str,
) -> Result<GpuCanvasContext, JsValue> {
    let ctx: GpuCanvasContext = canvas
        .get_context("webgpu")?
        .ok_or_else(|| JsValue::from_str("Could not get WebGPU context"))?
        .dyn_into()?;

    let config = web_sys::GpuCanvasConfiguration::new(device, str_to_texture_format(format));
    ctx.configure(&config)?;
    Ok(ctx)
}

/// Convert string to GpuTextureFormat.
fn str_to_texture_format(s: &str) -> web_sys::GpuTextureFormat {
    match s {
        "rgba8unorm" => web_sys::GpuTextureFormat::Rgba8unorm,
        "rgba8unorm-srgb" => web_sys::GpuTextureFormat::Rgba8unormSrgb,
        "bgra8unorm" => web_sys::GpuTextureFormat::Bgra8unorm,
        "bgra8unorm-srgb" => web_sys::GpuTextureFormat::Bgra8unormSrgb,
        "rgba16float" => web_sys::GpuTextureFormat::Rgba16float,
        _ => web_sys::GpuTextureFormat::Bgra8unorm,
    }
}

/// Get the command queue from a device.
#[wasm_bindgen]
pub fn get_queue(device: &GpuDevice) -> GpuQueue {
    device.queue()
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // device info
// ═══════════════════════════════════════════════════════════════════════════════

/// Get device limits.
#[wasm_bindgen]
pub fn get_limits(device: &GpuDevice) -> GpuSupportedLimits {
    device.limits()
}

/// Get device features as array of strings.
#[wasm_bindgen]
pub fn get_features(device: &GpuDevice) -> Array {
    let features: GpuSupportedFeatures = device.features();
    // GpuSupportedFeatures implements IntoIterator
    let arr = Array::new();
    for feature in features.values() {
        if let Ok(val) = feature {
            arr.push(&val);
        }
    }
    arr
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // error handling
// ═══════════════════════════════════════════════════════════════════════════════

/// Register callback for uncaptured errors.
/// Returns error if event listener registration fails.
#[wasm_bindgen]
pub fn on_uncaptured_error(device: &GpuDevice, callback: &js_sys::Function) -> Result<(), JsValue> {
    let cb = callback.clone();
    let closure = Closure::wrap(Box::new(move |event: web_sys::Event| {
        // Extract error from event, propagate to callback
        // Callback errors are logged but not propagated (async context)
        if let Ok(error) = Reflect::get(&event, &"error".into()) {
            if let Err(e) = cb.call1(&JsValue::NULL, &error) {
                web_sys::console::error_1(&e);
            }
        }
    }) as Box<dyn FnMut(web_sys::Event)>);

    device.add_event_listener_with_callback("uncapturederror", closure.as_ref().unchecked_ref())?;
    closure.forget();
    Ok(())
}

/// Register callback for device lost.
/// Returns the promise for chaining.
#[wasm_bindgen]
pub fn on_device_lost(device: &GpuDevice, callback: &js_sys::Function) -> JsValue {
    let cb = callback.clone();
    let closure = Closure::wrap(Box::new(move |info: GpuDeviceLostInfo| {
        let reason: JsValue = info.reason().into();
        // Callback errors are logged but not propagated (async context)
        if let Err(e) = cb.call1(&JsValue::NULL, &reason) {
            web_sys::console::error_1(&e);
        }
    }) as Box<dyn FnMut(GpuDeviceLostInfo)>);

    let lost_promise = device.lost();
    let result = lost_promise.then(&closure);
    closure.forget();
    result.into()
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // canvas operations
// ═══════════════════════════════════════════════════════════════════════════════

/// Get the current texture from canvas context.
#[wasm_bindgen]
pub fn get_current_texture(ctx: &GpuCanvasContext) -> Result<GpuTexture, JsValue> {
    ctx.get_current_texture()
}

/// Get preferred canvas format.
#[wasm_bindgen]
pub fn get_preferred_canvas_format() -> Result<String, JsValue> {
    let gpu = get_gpu().ok_or_else(|| JsValue::from_str("WebGPU not supported"))?;
    let format = gpu.get_preferred_canvas_format();
    Ok(format_to_string(format))
}

/// Convert GpuTextureFormat to string.
fn format_to_string(f: web_sys::GpuTextureFormat) -> String {
    match f {
        web_sys::GpuTextureFormat::Rgba8unorm => "rgba8unorm".to_string(),
        web_sys::GpuTextureFormat::Rgba8unormSrgb => "rgba8unorm-srgb".to_string(),
        web_sys::GpuTextureFormat::Bgra8unorm => "bgra8unorm".to_string(),
        web_sys::GpuTextureFormat::Bgra8unormSrgb => "bgra8unorm-srgb".to_string(),
        _ => "bgra8unorm".to_string(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // buffer operations
// ═══════════════════════════════════════════════════════════════════════════════

/// Create a GPU buffer.
#[wasm_bindgen]
pub fn create_buffer(device: &GpuDevice, desc: &Object) -> Result<GpuBuffer, JsValue> {
    device.create_buffer(&desc.clone().unchecked_into())
}

/// Destroy a GPU buffer.
#[wasm_bindgen]
pub fn destroy_buffer(buffer: &GpuBuffer) {
    buffer.destroy();
}

/// Write data to a buffer via queue.
#[wasm_bindgen]
pub fn write_buffer(
    queue: &GpuQueue,
    buffer: &GpuBuffer,
    buffer_offset: f64,
    data: &js_sys::Uint8Array,
    data_offset: f64,
    size: f64,
) -> Result<(), JsValue> {
    if size == 0.0 {
        queue.write_buffer_with_u32_and_buffer_source(buffer, buffer_offset as u32, &data.buffer())
    } else {
        queue.write_buffer_with_f64_and_buffer_source_and_f64_and_f64(
            buffer,
            buffer_offset,
            &data.buffer(),
            data_offset,
            size,
        )
    }
}

/// Map a buffer asynchronously.
#[wasm_bindgen]
pub fn map_buffer_async(buffer: &GpuBuffer, mode: u32, offset: f64, size: f64) -> JsValue {
    buffer.map_async_with_f64_and_f64(mode, offset, size).into()
}

/// Unmap a buffer.
#[wasm_bindgen]
pub fn unmap_buffer(buffer: &GpuBuffer) {
    buffer.unmap();
}

/// Get mapped range from buffer.
#[wasm_bindgen]
pub fn get_mapped_range(
    buffer: &GpuBuffer,
    offset: f64,
    size: f64,
) -> Result<js_sys::ArrayBuffer, JsValue> {
    buffer.get_mapped_range_with_f64_and_f64(offset, size)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // texture operations
// ═══════════════════════════════════════════════════════════════════════════════

/// Create a GPU texture.
#[wasm_bindgen]
pub fn create_texture(device: &GpuDevice, desc: &Object) -> Result<GpuTexture, JsValue> {
    device.create_texture(&desc.clone().unchecked_into())
}

/// Destroy a GPU texture.
#[wasm_bindgen]
pub fn destroy_texture(texture: &GpuTexture) {
    texture.destroy();
}

/// Create a texture view.
#[wasm_bindgen]
pub fn create_texture_view(texture: &GpuTexture, desc: &Object) -> Result<GpuTextureView, JsValue> {
    if desc.is_undefined() || desc.is_null() {
        texture.create_view()
    } else {
        texture.create_view_with_descriptor(&desc.clone().unchecked_into())
    }
}

/// Write data to a texture via queue.
#[wasm_bindgen]
pub fn write_texture(
    queue: &GpuQueue,
    dest: &Object,
    data: &js_sys::Uint8Array,
    data_layout: &Object,
    size: &Object,
) -> Result<(), JsValue> {
    queue.write_texture_with_buffer_source_and_gpu_extent_3d_dict(
        &dest.clone().unchecked_into(),
        &data.buffer(),
        &data_layout.clone().unchecked_into(),
        &size.clone().unchecked_into(),
    )
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // sampler operations
// ═══════════════════════════════════════════════════════════════════════════════

/// Create a GPU sampler.
#[wasm_bindgen]
pub fn create_sampler(device: &GpuDevice, desc: &Object) -> GpuSampler {
    device.create_sampler_with_descriptor(&desc.clone().unchecked_into())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // shader operations
// ═════════════════════════════════════════════════════════════��═════════════════

/// Create a shader module.
#[wasm_bindgen]
pub fn create_shader_module(device: &GpuDevice, desc: &Object) -> GpuShaderModule {
    device.create_shader_module(&desc.clone().unchecked_into())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // pipeline operations
// ═══════════════════════════════════════════════════════════════════════════════

/// Create a render pipeline.
#[wasm_bindgen]
pub fn create_render_pipeline(
    device: &GpuDevice,
    desc: &Object,
) -> Result<GpuRenderPipeline, JsValue> {
    device.create_render_pipeline(&desc.clone().unchecked_into())
}

/// Create a compute pipeline.
#[wasm_bindgen]
pub fn create_compute_pipeline(device: &GpuDevice, desc: &Object) -> GpuComputePipeline {
    device.create_compute_pipeline(&desc.clone().unchecked_into())
}

/// Create a bind group layout.
#[wasm_bindgen]
pub fn create_bind_group_layout(device: &GpuDevice, desc: &Object) -> Result<JsValue, JsValue> {
    Ok(device
        .create_bind_group_layout(&desc.clone().unchecked_into())?
        .into())
}

/// Create a pipeline layout.
#[wasm_bindgen]
pub fn create_pipeline_layout(device: &GpuDevice, desc: &Object) -> GpuPipelineLayout {
    device.create_pipeline_layout(&desc.clone().unchecked_into())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                       // bind group operations
// ═══════════════════════════════════════════════════════════════════════════════

/// Create a bind group.
#[wasm_bindgen]
pub fn create_bind_group(device: &GpuDevice, desc: &Object) -> JsValue {
    device
        .create_bind_group(&desc.clone().unchecked_into())
        .into()
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // command encoding
// ═══════════════════════════════════════════════════════════════════════════════

/// Create a command encoder.
#[wasm_bindgen]
pub fn create_command_encoder(device: &GpuDevice) -> GpuCommandEncoder {
    device.create_command_encoder()
}

/// Finish command encoder, returning command buffer.
#[wasm_bindgen]
pub fn finish_command_encoder(encoder: &GpuCommandEncoder) -> GpuCommandBuffer {
    encoder.finish()
}

/// Begin a render pass.
#[wasm_bindgen]
pub fn begin_render_pass(
    encoder: &GpuCommandEncoder,
    desc: &Object,
) -> Result<GpuRenderPassEncoder, JsValue> {
    encoder.begin_render_pass(&desc.clone().unchecked_into())
}

/// End a render pass.
#[wasm_bindgen]
pub fn end_render_pass(pass: &GpuRenderPassEncoder) {
    pass.end();
}

/// Begin a compute pass.
#[wasm_bindgen]
pub fn begin_compute_pass(encoder: &GpuCommandEncoder) -> GpuComputePassEncoder {
    encoder.begin_compute_pass()
}

/// End a compute pass.
#[wasm_bindgen]
pub fn end_compute_pass(pass: &GpuComputePassEncoder) {
    pass.end();
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                     // render pass operations
// ═══════════════════════════════════════════════════════════════════════════════

/// Set the render pipeline.
#[wasm_bindgen]
pub fn set_pipeline(pass: &GpuRenderPassEncoder, pipeline: &GpuRenderPipeline) {
    pass.set_pipeline(pipeline);
}

/// Set a bind group.
#[wasm_bindgen]
pub fn set_bind_group(pass: &GpuRenderPassEncoder, index: u32, bind_group: &JsValue) {
    pass.set_bind_group(index, Some(&bind_group.clone().unchecked_into()));
}

/// Set a vertex buffer.
#[wasm_bindgen]
pub fn set_vertex_buffer(
    pass: &GpuRenderPassEncoder,
    slot: u32,
    buffer: &GpuBuffer,
    offset: f64,
    size: f64,
) {
    if size == 0.0 {
        pass.set_vertex_buffer_with_f64(slot, Some(buffer), offset);
    } else {
        pass.set_vertex_buffer_with_f64_and_f64(slot, Some(buffer), offset, size);
    }
}

/// Set the index buffer.
#[wasm_bindgen]
pub fn set_index_buffer(
    pass: &GpuRenderPassEncoder,
    buffer: &GpuBuffer,
    format: &str,
    offset: f64,
    size: f64,
) {
    let fmt = match format {
        "uint16" => web_sys::GpuIndexFormat::Uint16,
        _ => web_sys::GpuIndexFormat::Uint32,
    };
    if size == 0.0 {
        pass.set_index_buffer_with_f64(buffer, fmt, offset);
    } else {
        pass.set_index_buffer_with_f64_and_f64(buffer, fmt, offset, size);
    }
}

/// Draw primitives.
#[wasm_bindgen]
pub fn draw(
    pass: &GpuRenderPassEncoder,
    vertex_count: u32,
    instance_count: u32,
    first_vertex: u32,
    first_instance: u32,
) {
    pass.draw_with_instance_count_and_first_vertex_and_first_instance(
        vertex_count,
        instance_count,
        first_vertex,
        first_instance,
    );
}

/// Draw indexed primitives.
#[wasm_bindgen]
pub fn draw_indexed(
    pass: &GpuRenderPassEncoder,
    index_count: u32,
    instance_count: u32,
    first_index: u32,
    base_vertex: i32,
    first_instance: u32,
) {
    pass.draw_indexed_with_instance_count_and_first_index_and_base_vertex_and_first_instance(
        index_count,
        instance_count,
        first_index,
        base_vertex,
        first_instance,
    );
}

/// Draw indirect.
#[wasm_bindgen]
pub fn draw_indirect(pass: &GpuRenderPassEncoder, buffer: &GpuBuffer, offset: f64) {
    pass.draw_indirect_with_f64(buffer, offset);
}

/// Set viewport.
#[wasm_bindgen]
pub fn set_viewport(
    pass: &GpuRenderPassEncoder,
    x: f32,
    y: f32,
    width: f32,
    height: f32,
    min_depth: f32,
    max_depth: f32,
) {
    pass.set_viewport(x, y, width, height, min_depth, max_depth);
}

/// Set scissor rect.
#[wasm_bindgen]
pub fn set_scissor_rect(pass: &GpuRenderPassEncoder, x: u32, y: u32, width: u32, height: u32) {
    pass.set_scissor_rect(x, y, width, height);
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // queue operations
// ═══════════════════════════════════════════════════════════════════════════════

/// Submit command buffers to the queue.
#[wasm_bindgen]
pub fn submit(queue: &GpuQueue, command_buffers: &Array) {
    // Convert Array to Vec<GpuCommandBuffer>
    let mut buffers: Vec<GpuCommandBuffer> = Vec::new();
    for i in 0..command_buffers.length() {
        if let Ok(buf) = command_buffers.get(i).dyn_into::<GpuCommandBuffer>() {
            buffers.push(buf);
        }
    }
    queue.submit(&buffers);
}
