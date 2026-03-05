//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                           // hydrogen // runtime // renderer
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! WebGPU renderer for Hydrogen command buffers.
//!
//! Uses raw web-sys WebGPU bindings (no wgpu crate).
//! This ensures no enum conflicts with webgpu.rs.
//!
//! This module is only compiled for WASM targets since it requires WebGPU.

#[cfg(target_arch = "wasm32")]
use std::collections::HashMap;

#[cfg(target_arch = "wasm32")]
use js_sys::{Array, Object, Reflect};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::JsCast;

#[cfg(target_arch = "wasm32")]
use web_sys::{
    Gpu, GpuAdapter, GpuBuffer, GpuCanvasContext, GpuDevice,
    GpuQueue, GpuRenderPipeline, GpuShaderModule, HtmlCanvasElement,
};

// WebGPU buffer usage flags (from spec)
// https://www.w3.org/TR/webgpu/#buffer-usage
const GPU_BUFFER_USAGE_VERTEX: u32 = 0x0020;
const GPU_BUFFER_USAGE_UNIFORM: u32 = 0x0040;
const GPU_BUFFER_USAGE_COPY_DST: u32 = 0x0008;

// WebGPU shader stage flags
const GPU_SHADER_STAGE_VERTEX: u32 = 0x1;
const GPU_SHADER_STAGE_FRAGMENT: u32 = 0x2;

#[cfg(target_arch = "wasm32")]
use crate::commands::{CommandBuffer, DrawCommand, GlyphInstancePayload, PathDataHeader};

#[cfg(target_arch = "wasm32")]
use crate::shaders;

#[cfg(target_arch = "wasm32")]
use crate::tessellate::{tessellate_contours, tessellate_path_commands, TessellatedPath};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // vertex types
// ═══════════════════════════════════════════════════════════════════════════════

/// Vertex for rect rendering.
#[cfg(target_arch = "wasm32")]
#[repr(C)]
#[derive(Copy, Clone, Debug, bytemuck::Pod, bytemuck::Zeroable)]
struct RectVertex {
    position: [f32; 2],
    rect: [f32; 4],
    color: [f32; 4],
    radii: [f32; 4],
    depth_pick: [f32; 2],
}

/// Vertex for path rendering (typography as geometry).
#[cfg(target_arch = "wasm32")]
#[repr(C)]
#[derive(Copy, Clone, Debug, bytemuck::Pod, bytemuck::Zeroable)]
struct PathVertex {
    position: [f32; 2],
    transform: [f32; 4],
    rotation: [f32; 3],
    _pad: f32,
    color: [f32; 4],
    depth_pick: [f32; 2],
}

/// Vertex for pick rendering.
#[cfg(target_arch = "wasm32")]
#[repr(C)]
#[derive(Copy, Clone, Debug, bytemuck::Pod, bytemuck::Zeroable)]
struct PickVertex {
    position: [f32; 2],
    rect: [f32; 4],
    pick_id: f32,
}

/// Vertex for particle rendering.
#[cfg(target_arch = "wasm32")]
#[repr(C)]
#[derive(Copy, Clone, Debug, bytemuck::Pod, bytemuck::Zeroable)]
struct ParticleVertex {
    position: [f32; 3],
    size: f32,
    color: [f32; 4],
    pick_id: f32,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // path data cache
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(target_arch = "wasm32")]
#[derive(Debug)]
struct CachedPathData {
    tessellated: TessellatedPath,
    header: PathDataHeader,
}

#[cfg(target_arch = "wasm32")]
#[derive(Debug, Default)]
struct PathDataCache {
    entries: HashMap<u32, CachedPathData>,
}

#[cfg(target_arch = "wasm32")]
impl PathDataCache {
    fn new() -> Self {
        PathDataCache {
            entries: HashMap::new(),
        }
    }

    fn insert(&mut self, id: u32, header: PathDataHeader, tessellated: TessellatedPath) {
        self.entries.insert(id, CachedPathData { tessellated, header });
    }

    fn get(&self, id: u32) -> Option<&CachedPathData> {
        self.entries.get(&id)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // pick regions
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(target_arch = "wasm32")]
#[derive(Debug, Clone, Copy)]
struct PickRegion {
    x: f32,
    y: f32,
    width: f32,
    height: f32,
    depth: f32,
    pick_id: u32,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // helpers
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(target_arch = "wasm32")]
fn get_gpu() -> Result<Gpu, JsValue> {
    let window = web_sys::window().ok_or_else(|| JsValue::from_str("No window"))?;
    let navigator = window.navigator();
    let gpu_val = Reflect::get(&navigator, &"gpu".into())?;
    if gpu_val.is_undefined() || gpu_val.is_null() {
        return Err(JsValue::from_str("WebGPU not supported"));
    }
    gpu_val.dyn_into::<Gpu>()
}

/// Create a JS object for pipeline descriptor building.
#[cfg(target_arch = "wasm32")]
fn js_obj() -> Object {
    Object::new()
}

/// Set a property on a JS object.
#[cfg(target_arch = "wasm32")]
fn set_prop(obj: &Object, key: &str, val: impl Into<JsValue>) -> Result<(), JsValue> {
    Reflect::set(obj, &key.into(), &val.into())?;
    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // renderer
// ═══════════════════════════════════════════════════════════════════════════════

/// The WebGPU renderer using raw web-sys bindings.
#[cfg(target_arch = "wasm32")]
pub struct Renderer {
    device: GpuDevice,
    queue: GpuQueue,
    context: GpuCanvasContext,
    format: web_sys::GpuTextureFormat,
    rect_pipeline: GpuRenderPipeline,
    path_pipeline: GpuRenderPipeline,
    pick_pipeline: GpuRenderPipeline,
    particle_pipeline: GpuRenderPipeline,
    uniform_buffer: GpuBuffer,
    uniform_bind_group: JsValue,
    width: u32,
    height: u32,
    path_data_cache: PathDataCache,
    pick_regions: Vec<PickRegion>,
}

#[cfg(target_arch = "wasm32")]
impl Renderer {
    /// Create a new renderer attached to a canvas element.
    pub async fn new(canvas: HtmlCanvasElement) -> Result<Self, String> {
        let width = canvas.width();
        let height = canvas.height();

        // Get GPU
        let gpu = get_gpu().map_err(|e| format!("GPU error: {:?}", e))?;

        // Request adapter
        let adapter_promise = gpu.request_adapter();
        let adapter: GpuAdapter = wasm_bindgen_futures::JsFuture::from(adapter_promise)
            .await
            .map_err(|e| format!("Adapter error: {:?}", e))?
            .dyn_into()
            .map_err(|_| "Failed to cast adapter")?;

        // Request device
        let device_promise = adapter.request_device();
        let device: GpuDevice = wasm_bindgen_futures::JsFuture::from(device_promise)
            .await
            .map_err(|e| format!("Device error: {:?}", e))?
            .dyn_into()
            .map_err(|_| "Failed to cast device")?;

        let queue = device.queue();

        // Get canvas context
        let context: GpuCanvasContext = canvas
            .get_context("webgpu")
            .map_err(|e| format!("Context error: {:?}", e))?
            .ok_or("No WebGPU context")?
            .dyn_into()
            .map_err(|_| "Failed to cast context")?;

        // Get preferred format
        let format = gpu.get_preferred_canvas_format();

        // Configure canvas
        let config = web_sys::GpuCanvasConfiguration::new(&device, format);
        context.configure(&config).map_err(|e| format!("Configure error: {:?}", e))?;

        // Create uniform buffer (resolution)
        let uniform_data: [f32; 4] = [width as f32, height as f32, 0.0, 0.0];
        let uniform_buffer = Self::create_buffer_init(
            &device,
            &uniform_data,
            GPU_BUFFER_USAGE_UNIFORM | GPU_BUFFER_USAGE_COPY_DST,
        )?;

        // Create bind group layout
        let bind_group_layout = Self::create_uniform_bind_group_layout(&device)?;

        // Create bind group
        let uniform_bind_group = Self::create_uniform_bind_group(&device, &bind_group_layout, &uniform_buffer)?;

        // Create pipeline layout
        let pipeline_layout = Self::create_pipeline_layout(&device, &bind_group_layout)?;

        // Create shaders and pipelines
        let rect_pipeline = Self::create_rect_pipeline(&device, &pipeline_layout, format)?;
        let path_pipeline = Self::create_path_pipeline(&device, &pipeline_layout, format)?;
        let pick_pipeline = Self::create_pick_pipeline(&device, &pipeline_layout)?;
        let particle_pipeline = Self::create_particle_pipeline(&device, &pipeline_layout, format)?;

        Ok(Renderer {
            device,
            queue,
            context,
            format,
            rect_pipeline,
            path_pipeline,
            pick_pipeline,
            particle_pipeline,
            uniform_buffer,
            uniform_bind_group,
            width,
            height,
            path_data_cache: PathDataCache::new(),
            pick_regions: Vec::new(),
        })
    }

    /// Create a buffer and initialize it with data.
    fn create_buffer_init<T: bytemuck::Pod>(
        device: &GpuDevice,
        data: &[T],
        usage: u32,
    ) -> Result<GpuBuffer, String> {
        let bytes = bytemuck::cast_slice(data);
        let size = bytes.len() as u64;

        // Buffer size must be multiple of 4
        let aligned_size = ((size + 3) & !3) as f64;

        let desc = web_sys::GpuBufferDescriptor::new_with_f64(aligned_size, usage);
        desc.set_mapped_at_creation(true);

        let buffer = device
            .create_buffer(&desc)
            .map_err(|e| format!("Buffer creation error: {:?}", e))?;

        // Copy data to mapped range
        let mapped = buffer
            .get_mapped_range()
            .map_err(|e| format!("Mapping error: {:?}", e))?;
        let array = js_sys::Uint8Array::new(&mapped);
        array.copy_from(bytes);
        buffer.unmap();

        Ok(buffer)
    }

    /// Create the uniform bind group layout.
    fn create_uniform_bind_group_layout(device: &GpuDevice) -> Result<web_sys::GpuBindGroupLayout, String> {
        let entry = js_obj();
        set_prop(&entry, "binding", 0).map_err(|e| format!("{:?}", e))?;
        set_prop(&entry, "visibility", GPU_SHADER_STAGE_VERTEX | GPU_SHADER_STAGE_FRAGMENT)
            .map_err(|e| format!("{:?}", e))?;

        let buffer_binding = js_obj();
        set_prop(&buffer_binding, "type", "uniform").map_err(|e| format!("{:?}", e))?;
        set_prop(&entry, "buffer", buffer_binding).map_err(|e| format!("{:?}", e))?;

        let entries = Array::new();
        entries.push(&entry);

        let desc = js_obj();
        set_prop(&desc, "entries", entries).map_err(|e| format!("{:?}", e))?;

        device
            .create_bind_group_layout(&desc.unchecked_into())
            .map_err(|e| format!("Bind group layout error: {:?}", e))
    }

    /// Create the uniform bind group.
    fn create_uniform_bind_group(
        device: &GpuDevice,
        layout: &web_sys::GpuBindGroupLayout,
        buffer: &GpuBuffer,
    ) -> Result<JsValue, String> {
        let entry = js_obj();
        set_prop(&entry, "binding", 0).map_err(|e| format!("{:?}", e))?;

        let resource = js_obj();
        set_prop(&resource, "buffer", buffer).map_err(|e| format!("{:?}", e))?;
        set_prop(&entry, "resource", resource).map_err(|e| format!("{:?}", e))?;

        let entries = Array::new();
        entries.push(&entry);

        let desc = js_obj();
        set_prop(&desc, "layout", layout).map_err(|e| format!("{:?}", e))?;
        set_prop(&desc, "entries", entries).map_err(|e| format!("{:?}", e))?;

        Ok(device.create_bind_group(&desc.unchecked_into()).into())
    }

    /// Create pipeline layout.
    fn create_pipeline_layout(
        device: &GpuDevice,
        bind_group_layout: &web_sys::GpuBindGroupLayout,
    ) -> Result<web_sys::GpuPipelineLayout, String> {
        let layouts = Array::new();
        layouts.push(bind_group_layout);

        let desc = js_obj();
        set_prop(&desc, "bindGroupLayouts", layouts).map_err(|e| format!("{:?}", e))?;

        Ok(device.create_pipeline_layout(&desc.unchecked_into()))
    }

    /// Create shader module from WGSL source.
    fn create_shader_module(device: &GpuDevice, code: &str) -> GpuShaderModule {
        let desc = web_sys::GpuShaderModuleDescriptor::new(code);
        device.create_shader_module(&desc)
    }

    /// Create vertex buffer layout for rect vertices.
    fn rect_vertex_layout() -> Object {
        // stride: 2 + 4 + 4 + 4 + 2 = 16 floats = 64 bytes
        let layout = js_obj();
        let _ = set_prop(&layout, "arrayStride", 64);
        let _ = set_prop(&layout, "stepMode", "vertex");

        let attrs = Array::new();
        // position: vec2<f32> at offset 0
        let attr0 = js_obj();
        let _ = set_prop(&attr0, "shaderLocation", 0);
        let _ = set_prop(&attr0, "offset", 0);
        let _ = set_prop(&attr0, "format", "float32x2");
        attrs.push(&attr0);

        // rect: vec4<f32> at offset 8
        let attr1 = js_obj();
        let _ = set_prop(&attr1, "shaderLocation", 1);
        let _ = set_prop(&attr1, "offset", 8);
        let _ = set_prop(&attr1, "format", "float32x4");
        attrs.push(&attr1);

        // color: vec4<f32> at offset 24
        let attr2 = js_obj();
        let _ = set_prop(&attr2, "shaderLocation", 2);
        let _ = set_prop(&attr2, "offset", 24);
        let _ = set_prop(&attr2, "format", "float32x4");
        attrs.push(&attr2);

        // radii: vec4<f32> at offset 40
        let attr3 = js_obj();
        let _ = set_prop(&attr3, "shaderLocation", 3);
        let _ = set_prop(&attr3, "offset", 40);
        let _ = set_prop(&attr3, "format", "float32x4");
        attrs.push(&attr3);

        // depth_pick: vec2<f32> at offset 56
        let attr4 = js_obj();
        let _ = set_prop(&attr4, "shaderLocation", 4);
        let _ = set_prop(&attr4, "offset", 56);
        let _ = set_prop(&attr4, "format", "float32x2");
        attrs.push(&attr4);

        let _ = set_prop(&layout, "attributes", attrs);
        layout
    }

    /// Create vertex buffer layout for path vertices.
    fn path_vertex_layout() -> Object {
        // stride: 2 + 4 + 3 + 1(pad) + 4 + 2 = 16 floats = 64 bytes
        let layout = js_obj();
        let _ = set_prop(&layout, "arrayStride", 64);
        let _ = set_prop(&layout, "stepMode", "vertex");

        let attrs = Array::new();
        // position: vec2<f32> at offset 0
        let attr0 = js_obj();
        let _ = set_prop(&attr0, "shaderLocation", 0);
        let _ = set_prop(&attr0, "offset", 0);
        let _ = set_prop(&attr0, "format", "float32x2");
        attrs.push(&attr0);

        // transform: vec4<f32> at offset 8
        let attr1 = js_obj();
        let _ = set_prop(&attr1, "shaderLocation", 1);
        let _ = set_prop(&attr1, "offset", 8);
        let _ = set_prop(&attr1, "format", "float32x4");
        attrs.push(&attr1);

        // rotation: vec3<f32> at offset 24
        let attr2 = js_obj();
        let _ = set_prop(&attr2, "shaderLocation", 2);
        let _ = set_prop(&attr2, "offset", 24);
        let _ = set_prop(&attr2, "format", "float32x3");
        attrs.push(&attr2);

        // color: vec4<f32> at offset 40 (after pad)
        let attr3 = js_obj();
        let _ = set_prop(&attr3, "shaderLocation", 3);
        let _ = set_prop(&attr3, "offset", 40);
        let _ = set_prop(&attr3, "format", "float32x4");
        attrs.push(&attr3);

        // depth_pick: vec2<f32> at offset 56
        let attr4 = js_obj();
        let _ = set_prop(&attr4, "shaderLocation", 4);
        let _ = set_prop(&attr4, "offset", 56);
        let _ = set_prop(&attr4, "format", "float32x2");
        attrs.push(&attr4);

        let _ = set_prop(&layout, "attributes", attrs);
        layout
    }

    /// Create vertex buffer layout for pick vertices.
    fn pick_vertex_layout() -> Object {
        // stride: 2 + 4 + 1 = 7 floats = 28 bytes
        let layout = js_obj();
        let _ = set_prop(&layout, "arrayStride", 28);
        let _ = set_prop(&layout, "stepMode", "vertex");

        let attrs = Array::new();
        let attr0 = js_obj();
        let _ = set_prop(&attr0, "shaderLocation", 0);
        let _ = set_prop(&attr0, "offset", 0);
        let _ = set_prop(&attr0, "format", "float32x2");
        attrs.push(&attr0);

        let attr1 = js_obj();
        let _ = set_prop(&attr1, "shaderLocation", 1);
        let _ = set_prop(&attr1, "offset", 8);
        let _ = set_prop(&attr1, "format", "float32x4");
        attrs.push(&attr1);

        let attr2 = js_obj();
        let _ = set_prop(&attr2, "shaderLocation", 2);
        let _ = set_prop(&attr2, "offset", 24);
        let _ = set_prop(&attr2, "format", "float32");
        attrs.push(&attr2);

        let _ = set_prop(&layout, "attributes", attrs);
        layout
    }

    /// Create vertex buffer layout for particle vertices.
    fn particle_vertex_layout() -> Object {
        // stride: 3 + 1 + 4 + 1 = 9 floats = 36 bytes
        let layout = js_obj();
        let _ = set_prop(&layout, "arrayStride", 36);
        let _ = set_prop(&layout, "stepMode", "instance");

        let attrs = Array::new();
        let attr0 = js_obj();
        let _ = set_prop(&attr0, "shaderLocation", 0);
        let _ = set_prop(&attr0, "offset", 0);
        let _ = set_prop(&attr0, "format", "float32x3");
        attrs.push(&attr0);

        let attr1 = js_obj();
        let _ = set_prop(&attr1, "shaderLocation", 1);
        let _ = set_prop(&attr1, "offset", 12);
        let _ = set_prop(&attr1, "format", "float32");
        attrs.push(&attr1);

        let attr2 = js_obj();
        let _ = set_prop(&attr2, "shaderLocation", 2);
        let _ = set_prop(&attr2, "offset", 16);
        let _ = set_prop(&attr2, "format", "float32x4");
        attrs.push(&attr2);

        let attr3 = js_obj();
        let _ = set_prop(&attr3, "shaderLocation", 3);
        let _ = set_prop(&attr3, "offset", 32);
        let _ = set_prop(&attr3, "format", "float32");
        attrs.push(&attr3);

        let _ = set_prop(&layout, "attributes", attrs);
        layout
    }

    /// Create the rect render pipeline.
    fn create_rect_pipeline(
        device: &GpuDevice,
        layout: &web_sys::GpuPipelineLayout,
        format: web_sys::GpuTextureFormat,
    ) -> Result<GpuRenderPipeline, String> {
        let shader = Self::create_shader_module(device, shaders::RECT_SHADER);

        let vertex = js_obj();
        let _ = set_prop(&vertex, "module", &shader);
        let _ = set_prop(&vertex, "entryPoint", "vs_main");
        let buffers = Array::new();
        buffers.push(&Self::rect_vertex_layout());
        let _ = set_prop(&vertex, "buffers", buffers);

        let blend = js_obj();
        let color_blend = js_obj();
        let _ = set_prop(&color_blend, "srcFactor", "src-alpha");
        let _ = set_prop(&color_blend, "dstFactor", "one-minus-src-alpha");
        let _ = set_prop(&color_blend, "operation", "add");
        let _ = set_prop(&blend, "color", color_blend);
        let alpha_blend = js_obj();
        let _ = set_prop(&alpha_blend, "srcFactor", "one");
        let _ = set_prop(&alpha_blend, "dstFactor", "one-minus-src-alpha");
        let _ = set_prop(&alpha_blend, "operation", "add");
        let _ = set_prop(&blend, "alpha", alpha_blend);

        let target = js_obj();
        let _ = set_prop(&target, "format", format_to_str(format));
        let _ = set_prop(&target, "blend", blend);

        let targets = Array::new();
        targets.push(&target);

        let fragment = js_obj();
        let _ = set_prop(&fragment, "module", &shader);
        let _ = set_prop(&fragment, "entryPoint", "fs_main");
        let _ = set_prop(&fragment, "targets", targets);

        let primitive = js_obj();
        let _ = set_prop(&primitive, "topology", "triangle-list");

        let desc = js_obj();
        let _ = set_prop(&desc, "layout", layout);
        let _ = set_prop(&desc, "vertex", vertex);
        let _ = set_prop(&desc, "fragment", fragment);
        let _ = set_prop(&desc, "primitive", primitive);

        device
            .create_render_pipeline(&desc.unchecked_into())
            .map_err(|e| format!("Rect pipeline error: {:?}", e))
    }

    /// Create the path render pipeline.
    fn create_path_pipeline(
        device: &GpuDevice,
        layout: &web_sys::GpuPipelineLayout,
        format: web_sys::GpuTextureFormat,
    ) -> Result<GpuRenderPipeline, String> {
        let shader = Self::create_shader_module(device, shaders::PATH_SHADER);

        let vertex = js_obj();
        let _ = set_prop(&vertex, "module", &shader);
        let _ = set_prop(&vertex, "entryPoint", "vs_main");
        let buffers = Array::new();
        buffers.push(&Self::path_vertex_layout());
        let _ = set_prop(&vertex, "buffers", buffers);

        let blend = js_obj();
        let color_blend = js_obj();
        let _ = set_prop(&color_blend, "srcFactor", "src-alpha");
        let _ = set_prop(&color_blend, "dstFactor", "one-minus-src-alpha");
        let _ = set_prop(&color_blend, "operation", "add");
        let _ = set_prop(&blend, "color", color_blend);
        let alpha_blend = js_obj();
        let _ = set_prop(&alpha_blend, "srcFactor", "one");
        let _ = set_prop(&alpha_blend, "dstFactor", "one-minus-src-alpha");
        let _ = set_prop(&alpha_blend, "operation", "add");
        let _ = set_prop(&blend, "alpha", alpha_blend);

        let target = js_obj();
        let _ = set_prop(&target, "format", format_to_str(format));
        let _ = set_prop(&target, "blend", blend);

        let targets = Array::new();
        targets.push(&target);

        let fragment = js_obj();
        let _ = set_prop(&fragment, "module", &shader);
        let _ = set_prop(&fragment, "entryPoint", "fs_main");
        let _ = set_prop(&fragment, "targets", targets);

        let primitive = js_obj();
        let _ = set_prop(&primitive, "topology", "triangle-list");

        let desc = js_obj();
        let _ = set_prop(&desc, "layout", layout);
        let _ = set_prop(&desc, "vertex", vertex);
        let _ = set_prop(&desc, "fragment", fragment);
        let _ = set_prop(&desc, "primitive", primitive);

        device
            .create_render_pipeline(&desc.unchecked_into())
            .map_err(|e| format!("Path pipeline error: {:?}", e))
    }

    /// Create the pick render pipeline.
    fn create_pick_pipeline(
        device: &GpuDevice,
        layout: &web_sys::GpuPipelineLayout,
    ) -> Result<GpuRenderPipeline, String> {
        let shader = Self::create_shader_module(device, shaders::PICK_SHADER);

        let vertex = js_obj();
        let _ = set_prop(&vertex, "module", &shader);
        let _ = set_prop(&vertex, "entryPoint", "vs_main");
        let buffers = Array::new();
        buffers.push(&Self::pick_vertex_layout());
        let _ = set_prop(&vertex, "buffers", buffers);

        let target = js_obj();
        let _ = set_prop(&target, "format", "rgba8unorm");

        let targets = Array::new();
        targets.push(&target);

        let fragment = js_obj();
        let _ = set_prop(&fragment, "module", &shader);
        let _ = set_prop(&fragment, "entryPoint", "fs_main");
        let _ = set_prop(&fragment, "targets", targets);

        let primitive = js_obj();
        let _ = set_prop(&primitive, "topology", "triangle-list");

        let desc = js_obj();
        let _ = set_prop(&desc, "layout", layout);
        let _ = set_prop(&desc, "vertex", vertex);
        let _ = set_prop(&desc, "fragment", fragment);
        let _ = set_prop(&desc, "primitive", primitive);

        device
            .create_render_pipeline(&desc.unchecked_into())
            .map_err(|e| format!("Pick pipeline error: {:?}", e))
    }

    /// Create the particle render pipeline.
    fn create_particle_pipeline(
        device: &GpuDevice,
        layout: &web_sys::GpuPipelineLayout,
        format: web_sys::GpuTextureFormat,
    ) -> Result<GpuRenderPipeline, String> {
        let shader = Self::create_shader_module(device, shaders::PARTICLE_SHADER);

        let vertex = js_obj();
        let _ = set_prop(&vertex, "module", &shader);
        let _ = set_prop(&vertex, "entryPoint", "vs_main");
        let buffers = Array::new();
        buffers.push(&Self::particle_vertex_layout());
        let _ = set_prop(&vertex, "buffers", buffers);

        let blend = js_obj();
        let color_blend = js_obj();
        let _ = set_prop(&color_blend, "srcFactor", "src-alpha");
        let _ = set_prop(&color_blend, "dstFactor", "one-minus-src-alpha");
        let _ = set_prop(&color_blend, "operation", "add");
        let _ = set_prop(&blend, "color", color_blend);
        let alpha_blend = js_obj();
        let _ = set_prop(&alpha_blend, "srcFactor", "one");
        let _ = set_prop(&alpha_blend, "dstFactor", "one-minus-src-alpha");
        let _ = set_prop(&alpha_blend, "operation", "add");
        let _ = set_prop(&blend, "alpha", alpha_blend);

        let target = js_obj();
        let _ = set_prop(&target, "format", format_to_str(format));
        let _ = set_prop(&target, "blend", blend);

        let targets = Array::new();
        targets.push(&target);

        let fragment = js_obj();
        let _ = set_prop(&fragment, "module", &shader);
        let _ = set_prop(&fragment, "entryPoint", "fs_main");
        let _ = set_prop(&fragment, "targets", targets);

        let primitive = js_obj();
        let _ = set_prop(&primitive, "topology", "triangle-list");

        let desc = js_obj();
        let _ = set_prop(&desc, "layout", layout);
        let _ = set_prop(&desc, "vertex", vertex);
        let _ = set_prop(&desc, "fragment", fragment);
        let _ = set_prop(&desc, "primitive", primitive);

        device
            .create_render_pipeline(&desc.unchecked_into())
            .map_err(|e| format!("Particle pipeline error: {:?}", e))
    }

    /// Render a command buffer.
    pub fn render(&mut self, buffer: &CommandBuffer) -> Result<(), String> {
        // Process path definitions first
        self.process_path_definitions(buffer);

        // Get current texture
        let texture = self.context.get_current_texture()
            .map_err(|e| format!("Texture error: {:?}", e))?;
        let view = texture.create_view()
            .map_err(|e| format!("View error: {:?}", e))?;

        // Collect commands by type
        let rects: Vec<_> = buffer.commands.iter().filter_map(|cmd| {
            if let DrawCommand::Rect(r) = cmd { Some(*r) } else { None }
        }).collect();

        let glyph_instances: Vec<_> = buffer.commands.iter().filter_map(|cmd| {
            if let DrawCommand::GlyphInstance(g) = cmd { Some(*g) } else { None }
        }).collect();

        let particles: Vec<_> = buffer.commands.iter().filter_map(|cmd| {
            if let DrawCommand::Particle(p) = cmd { Some(*p) } else { None }
        }).collect();

        // Build vertices
        let rect_vertices = self.build_rect_vertices(&rects);
        let path_vertices = self.build_path_vertices(&glyph_instances);
        let particle_vertices = self.build_particle_vertices(&particles);

        // Update pick regions
        self.update_pick_regions(&rects, &glyph_instances);

        // Early return if nothing to draw
        if rect_vertices.is_empty() && path_vertices.is_empty() && particle_vertices.is_empty() {
            texture.destroy();
            return Ok(());
        }

        // Create vertex buffers
        let rect_buffer = if !rect_vertices.is_empty() {
            Some(Self::create_buffer_init(&self.device, &rect_vertices, GPU_BUFFER_USAGE_VERTEX)?)
        } else {
            None
        };

        let path_buffer = if !path_vertices.is_empty() {
            Some(Self::create_buffer_init(&self.device, &path_vertices, GPU_BUFFER_USAGE_VERTEX)?)
        } else {
            None
        };

        let particle_buffer = if !particle_vertices.is_empty() {
            Some(Self::create_buffer_init(&self.device, &particle_vertices, GPU_BUFFER_USAGE_VERTEX)?)
        } else {
            None
        };

        // Create command encoder
        let encoder = self.device.create_command_encoder();

        // Begin render pass
        let color_attachment = js_obj();
        let _ = set_prop(&color_attachment, "view", &view);
        let _ = set_prop(&color_attachment, "loadOp", "clear");
        let _ = set_prop(&color_attachment, "storeOp", "store");

        let clear_color = js_obj();
        let _ = set_prop(&clear_color, "r", 0.0);
        let _ = set_prop(&clear_color, "g", 0.0);
        let _ = set_prop(&clear_color, "b", 0.0);
        let _ = set_prop(&clear_color, "a", 1.0);
        let _ = set_prop(&color_attachment, "clearValue", clear_color);

        let color_attachments = Array::new();
        color_attachments.push(&color_attachment);

        let pass_desc = js_obj();
        let _ = set_prop(&pass_desc, "colorAttachments", color_attachments);

        let pass = encoder.begin_render_pass(&pass_desc.unchecked_into())
            .map_err(|e| format!("Render pass error: {:?}", e))?;

        // Draw rects
        if let Some(ref buf) = rect_buffer {
            pass.set_pipeline(&self.rect_pipeline);
            pass.set_bind_group(0, Some(&self.uniform_bind_group.clone().unchecked_into()));
            pass.set_vertex_buffer(0, Some(buf));
            pass.draw(rect_vertices.len() as u32);
        }

        // Draw paths
        if let Some(ref buf) = path_buffer {
            pass.set_pipeline(&self.path_pipeline);
            pass.set_bind_group(0, Some(&self.uniform_bind_group.clone().unchecked_into()));
            pass.set_vertex_buffer(0, Some(buf));
            pass.draw(path_vertices.len() as u32);
        }

        // Draw particles (instanced)
        if let Some(ref buf) = particle_buffer {
            pass.set_pipeline(&self.particle_pipeline);
            pass.set_bind_group(0, Some(&self.uniform_bind_group.clone().unchecked_into()));
            pass.set_vertex_buffer(0, Some(buf));
            pass.draw_with_instance_count(6, particle_vertices.len() as u32);
        }

        pass.end();

        // Submit
        let command_buffer = encoder.finish();
        self.queue.submit(&[command_buffer]);

        Ok(())
    }

    /// Process path data definitions.
    fn process_path_definitions(&mut self, buffer: &CommandBuffer) {
        for cmd in &buffer.commands {
            match cmd {
                DrawCommand::PathData { header, commands } => {
                    if self.path_data_cache.get(header.path_data_id).is_none() {
                        let tessellated = tessellate_path_commands(commands);
                        self.path_data_cache.insert(header.path_data_id, *header, tessellated);
                    }
                }
                DrawCommand::GlyphPath { header, contours } => {
                    if self.path_data_cache.get(header.glyph_id).is_none() {
                        let tessellated = tessellate_contours(contours);
                        let path_header = PathDataHeader {
                            path_data_id: header.glyph_id,
                            command_count: 0,
                            bounds: header.bounds,
                        };
                        self.path_data_cache.insert(header.glyph_id, path_header, tessellated);
                    }
                }
                _ => {}
            }
        }
    }

    /// Build rect vertices.
    fn build_rect_vertices(&self, rects: &[crate::commands::RectPayload]) -> Vec<RectVertex> {
        let mut vertices = Vec::with_capacity(rects.len() * 6);

        for rect in rects {
            let quad: [[f32; 2]; 6] = [
                [0.0, 0.0], [1.0, 0.0], [1.0, 1.0],
                [0.0, 0.0], [1.0, 1.0], [0.0, 1.0],
            ];

            for pos in quad {
                vertices.push(RectVertex {
                    position: pos,
                    rect: [rect.x, rect.y, rect.width, rect.height],
                    color: [rect.color.r, rect.color.g, rect.color.b, rect.color.a],
                    radii: [rect.radii.top_left, rect.radii.top_right, rect.radii.bottom_right, rect.radii.bottom_left],
                    depth_pick: [rect.depth, rect.pick_id as f32],
                });
            }
        }

        vertices
    }

    /// Build path vertices.
    fn build_path_vertices(&self, instances: &[GlyphInstancePayload]) -> Vec<PathVertex> {
        let mut vertices = Vec::new();

        for instance in instances {
            if let Some(cached) = self.path_data_cache.get(instance.path_data_id) {
                let tess = &cached.tessellated;
                let bounds = &cached.header.bounds;

                // Visibility culling
                let scaled_width = (bounds.max_x - bounds.min_x) * instance.scale_x;
                let scaled_height = (bounds.max_y - bounds.min_y) * instance.scale_y;
                let world_min_x = instance.pos_x + bounds.min_x * instance.scale_x;
                let world_min_y = instance.pos_y + bounds.min_y * instance.scale_y;
                let world_max_x = world_min_x + scaled_width;
                let world_max_y = world_min_y + scaled_height;

                if world_max_x < 0.0 || world_max_y < 0.0
                    || world_min_x > self.width as f32
                    || world_min_y > self.height as f32
                {
                    continue;
                }

                let color = [
                    instance.color.r as f32 / 255.0,
                    instance.color.g as f32 / 255.0,
                    instance.color.b as f32 / 255.0,
                    instance.color.a as f32 / 255.0,
                ];

                let transform = [instance.pos_x, instance.pos_y, instance.scale_x, instance.scale_y];
                let rotation = [instance.rot_x, instance.rot_y, instance.rot_z];
                let depth_pick = [instance.depth, instance.pick_id as f32];

                for i in (0..tess.indices.len()).step_by(3) {
                    for j in 0..3 {
                        let idx = tess.indices[i + j] as usize;
                        let vx = tess.vertices[idx * 2];
                        let vy = tess.vertices[idx * 2 + 1];

                        vertices.push(PathVertex {
                            position: [vx, vy],
                            transform,
                            rotation,
                            _pad: 0.0,
                            color,
                            depth_pick,
                        });
                    }
                }
            }
        }

        vertices
    }

    /// Build particle vertices.
    fn build_particle_vertices(&self, particles: &[crate::commands::ParticlePayload]) -> Vec<ParticleVertex> {
        particles.iter().map(|p| ParticleVertex {
            position: [p.x, p.y, p.z],
            size: p.size,
            color: [p.color.r, p.color.g, p.color.b, p.color.a],
            pick_id: p.pick_id as f32,
        }).collect()
    }

    /// Update pick regions for CPU-side hit testing.
    fn update_pick_regions(&mut self, rects: &[crate::commands::RectPayload], instances: &[GlyphInstancePayload]) {
        self.pick_regions.clear();

        for rect in rects {
            if rect.pick_id != 0 {
                self.pick_regions.push(PickRegion {
                    x: rect.x,
                    y: rect.y,
                    width: rect.width,
                    height: rect.height,
                    depth: rect.depth,
                    pick_id: rect.pick_id,
                });
            }
        }

        for instance in instances {
            if instance.pick_id != 0 {
                if let Some(cached) = self.path_data_cache.get(instance.path_data_id) {
                    let bounds = &cached.header.bounds;
                    let scaled_width = (bounds.max_x - bounds.min_x) * instance.scale_x;
                    let scaled_height = (bounds.max_y - bounds.min_y) * instance.scale_y;
                    self.pick_regions.push(PickRegion {
                        x: instance.pos_x + bounds.min_x * instance.scale_x,
                        y: instance.pos_y + bounds.min_y * instance.scale_y,
                        width: scaled_width,
                        height: scaled_height,
                        depth: instance.depth,
                        pick_id: instance.pick_id,
                    });
                }
            }
        }

        // Sort by depth (front-to-back)
        self.pick_regions.sort_by(|a, b| b.depth.total_cmp(&a.depth));
    }

    /// Pick element at screen coordinates.
    pub fn pick(&self, x: u32, y: u32) -> u32 {
        let px = x as f32;
        let py = y as f32;

        for region in &self.pick_regions {
            if px >= region.x && px < region.x + region.width
                && py >= region.y && py < region.y + region.height
            {
                return region.pick_id;
            }
        }

        0
    }

    /// Check if GPU picking is supported.
    pub fn has_gpu_pick_support(&self) -> bool {
        true
    }

    /// Resize the renderer.
    pub fn resize(&mut self, width: u32, height: u32) {
        if width == 0 || height == 0 {
            return;
        }

        self.width = width;
        self.height = height;

        // Update uniform buffer
        let uniform_data: [f32; 4] = [width as f32, height as f32, 0.0, 0.0];
        let bytes = bytemuck::cast_slice(&uniform_data);
        let _ = self.queue.write_buffer_with_u32_and_buffer_source(
            &self.uniform_buffer,
            0,
            &js_sys::Uint8Array::from(bytes).buffer(),
        );
    }
}

/// Convert GpuTextureFormat to string for JS descriptors.
#[cfg(target_arch = "wasm32")]
fn format_to_str(format: web_sys::GpuTextureFormat) -> &'static str {
    match format {
        web_sys::GpuTextureFormat::Rgba8unorm => "rgba8unorm",
        web_sys::GpuTextureFormat::Rgba8unormSrgb => "rgba8unorm-srgb",
        web_sys::GpuTextureFormat::Bgra8unorm => "bgra8unorm",
        web_sys::GpuTextureFormat::Bgra8unormSrgb => "bgra8unorm-srgb",
        web_sys::GpuTextureFormat::Rgba16float => "rgba16float",
        _ => "bgra8unorm",
    }
}
