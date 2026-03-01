# Pillar 11: Spatial

3D rendering, XR, PBR materials.

## Implementation

- **Location**: `src/Hydrogen/Schema/Spatial/`
- **Files**: 64 modules
- **Key features**: PBR materials, camera optics, lighting, XR tracking, scene graphs

## Atoms

### Camera Optics

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| FOV | Number | 1.0 | 179.0 | clamps | Vertical field of view in degrees |
| NearClip | Number | 0.001 | 1000.0 | clamps | Near clipping plane distance |
| FarClip | Number | 0.1 | 10000.0 | clamps | Far clipping plane distance |
| FocalLength | Number | 8.0 | 600.0 | clamps | Lens focal length in mm |
| SensorWidth | Number | 1.0 | - | clamps | Camera sensor width in mm |
| FocusDistance | Number | 0.0 | - | clamps | Focus distance for DOF |
| Aperture | Number | 1.0 | - | clamps | F-stop aperture |
| Exposure | Number | -10.0 | 10.0 | clamps | Exposure compensation in EV |

### PBR Material

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Metallic | Number | 0.0 | 1.0 | clamps | Metal vs dielectric (0=plastic, 1=metal) |
| Roughness | Number | 0.0 | 1.0 | clamps | Surface roughness (0=mirror, 1=matte) |
| IOR | Number | 1.0 | 4.0 | clamps | Index of refraction (1.5=glass, 2.42=diamond) |
| Transmission | Number | 0.0 | 1.0 | clamps | Light transmission (glass, water) |
| ClearCoat | Number | 0.0 | 1.0 | clamps | Clear coat intensity (car paint) |
| ClearCoatRoughness | Number | 0.0 | 1.0 | clamps | Clear coat roughness |
| Sheen | Number | 0.0 | 1.0 | clamps | Fabric sheen (velvet, silk) |
| Subsurface | Number | 0.0 | 1.0 | clamps | SSS intensity (skin, marble, wax) |
| Anisotropy | Number | -1.0 | 1.0 | clamps | Directional reflection (brushed metal) |
| Reflectance | Number | 0.0 | 1.0 | clamps | Dielectric reflectance |
| EmissiveStrength | Number | 0.0 | - | clamps | Emission intensity |

### Lighting

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| LightIntensity | Number | 0.0 | 10000.0 | clamps | Light intensity in nits |
| LightRange | Number | 0.0 | 1000.0 | clamps | Attenuation distance in meters |
| SpotAngle | Number | 0.0 | 180.0 | clamps | Spotlight cone angle in degrees |
| SpotSoftness | Number | 0.0 | 1.0 | clamps | Spotlight penumbra |
| ShadowBias | Number | - | - | - | Depth bias to prevent shadow acne |
| ShadowStrength | Number | 0.0 | 1.0 | clamps | Shadow opacity |

### Transform

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Position | Vec3 Number | - | - | - | 3D world position |
| Scale | Vec3 Number | - | - | - | 3D scale factors |
| AxisAngle | Number + Vec3 | - | - | - | Rotation as axis + angle |
| Gimbal | Pitch+Yaw+Roll | -90/360/360 | 90/360/360 | clamps/wraps | Euler rotation |

## Molecules

### Camera Types

| Name | Composition | Notes |
|------|-------------|-------|
| PerspectiveCamera | FOV + NearClip + FarClip | Standard 3D camera |
| OrthographicCamera | Size + NearClip + FarClip | No perspective distortion |
| PhysicalCamera | FocalLength + SensorWidth + Exposure + NearClip + FarClip | Matches real camera optics |

### Light Types

| Name | Composition | Notes |
|------|-------------|-------|
| DirectionalLight | Color + Intensity + Shadow | Sun-like infinite distance |
| PointLight | Color + Intensity + Range + Shadow | Omnidirectional bulb |
| SpotLight | Color + Intensity + Range + Angle + Softness + Shadow | Flashlight cone |
| AmbientLight | Color + Intensity | Base illumination |
| HemisphereLight | SkyColor + GroundColor + Intensity | Sky/ground gradient ambient |

### Shadow Configuration

| Name | Composition | Notes |
|------|-------------|-------|
| ShadowConfig | Bias + Strength + Resolution | Shadow map parameters |

### Viewport

| Name | Composition | Notes |
|------|-------------|-------|
| Viewport | PixelShape + LatentShape + PhysicalExtent | Tensor computation target |

## Compounds

### StandardSurface (MaterialX)

| Name | Description |
|------|-------------|
| Base | BaseWeight + BaseColor + DiffuseRoughness + Metalness |
| Specular | SpecularWeight + SpecularColor + SpecularRoughness + SpecularIOR + Anisotropy + Rotation |
| Transmission | TransmissionWeight + TransmissionColor + Depth + Dispersion |
| Subsurface | SubsurfaceWeight + SubsurfaceColor + Radius + Scale + Anisotropy |
| Sheen | SheenWeight + SheenColor + SheenRoughness |
| Coat | CoatWeight + CoatColor + CoatRoughness + CoatAnisotropy + CoatIOR |
| ThinFilm | ThinFilmThickness + ThinFilmIOR |
| Emission | EmissionWeight + EmissionColor |
| Geometry | Opacity + ThinWalled |
| StandardSurface | All layers combined (industry standard PBR) |

### Material Presets

| Name | Description |
|------|-------------|
| plastic | Standard dielectric with no metallic |
| metal | Full metallic with low roughness |
| glass | Transmissive with IOR 1.5 |
| skin | Subsurface scattering material |
| fabric | Sheen-based cloth material |
| carPaint | Clear coat over metallic base |

### Gizmo (3D Transform Controls)

| Name | Description |
|------|-------------|
| Gizmo | Interactive transform control (translate/rotate/scale) |
| GizmoMode | Translate, Rotate, Scale modes |
| GizmoSpace | Local, World, View coordinate spaces |
| GizmoHandle | X, Y, Z, XY, XZ, YZ, Center handles |

### SceneGraph

| Name | Description |
|------|-------------|
| Node | Scene graph node with transform hierarchy |
| Environment | Sky, fog, ambient lighting |

## XR (Extended Reality)

### Session Management

| Name | Description |
|------|-------------|
| XRSession | AR/VR session configuration (mode, features, reference space) |
| XRSessionMode | Inline, ImmersiveVR, ImmersiveAR |
| XRSessionFeature | HandTracking, HitTest, Anchors, PlaneDetection, etc. |
| XRReferenceSpace | Viewer, Local, LocalFloor, BoundedFloor, Unbounded |

### World Understanding

| Name | Description |
|------|-------------|
| XRAnchor | World-locked persistent position |
| XRPlane | Detected real-world surface (floor, wall, table) |
| XRMesh | Scanned environment geometry |

### Input Tracking

| Name | Description |
|------|-------------|
| XRHand | 25-joint hand tracking (WebXR spec) |
| XRController | 6DOF controller with buttons, triggers, haptics |
| XRHitTest | Raycast against real-world geometry |
| XRLight | Real-world light estimation (spherical harmonics) |

### Hand Joints (WebXR Spec)

| Joint | Description |
|-------|-------------|
| Wrist | Base of hand |
| Thumb (4) | Metacarpal, Proximal, Distal, Tip |
| Index (5) | Metacarpal, Proximal, Intermediate, Distal, Tip |
| Middle (5) | Metacarpal, Proximal, Intermediate, Distal, Tip |
| Ring (5) | Metacarpal, Proximal, Intermediate, Distal, Tip |
| Pinky (5) | Metacarpal, Proximal, Intermediate, Distal, Tip |

### Controller Profiles

| Name | Description |
|------|-------------|
| OculusTouch | Meta Quest controllers |
| ValveIndex | Valve Index Knuckles |
| HTCVive | HTC Vive wands |
| MicrosoftMixed | Windows MR controllers |
| PicoNeo | Pico Neo controllers |

## Design Philosophy

The Spatial pillar provides bounded primitives for 3D rendering and XR that enable **deterministic material exchange** between tools. All PBR parameters use exact bounds from MaterialX specification, ensuring same parameters = same rendered pixels across any renderer.

At billion-agent scale, agents compose materials from these bounded atoms. When an agent specifies `Metallic 0.8, Roughness 0.3`, the result is identical across Unreal, Unity, Blender, Arnold, or any other PBR renderer.
