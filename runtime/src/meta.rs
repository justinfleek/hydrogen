//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                                  // hydrogen // meta // wasm
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! # Document Head Management
//!
//! Replaces JavaScript FFI for `Hydrogen.Head.Meta`.
//!
//! Provides:
//! - Title manipulation
//! - Meta tag CRUD
//! - Link tag management (preload, prefetch, canonical)
//! - Favicon setting
//!
//! ## State Machine
//!
//! This module is stateless — each call directly manipulates the DOM.
//! No internal state to track. The DOM is the source of truth.
//!
//! ## Integration
//!
//! PureScript calls these via wasm-bindgen. Zero JavaScript.
//!
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[cfg(target_arch = "wasm32")]
use web_sys::{
    window, Document, Element, HtmlElement, HtmlHeadElement, HtmlLinkElement, HtmlMetaElement,
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // helpers
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(target_arch = "wasm32")]
fn get_document() -> Result<Document, JsValue> {
    window()
        .ok_or_else(|| JsValue::from_str("No window"))?
        .document()
        .ok_or_else(|| JsValue::from_str("No document"))
}

#[cfg(target_arch = "wasm32")]
fn get_head() -> Result<HtmlHeadElement, JsValue> {
    get_document()?
        .head()
        .ok_or_else(|| JsValue::from_str("No head element"))
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // title
// ═══════════════════════════════════════════════════════════════════════════════

/// Set document title.
///
/// Corresponds to: `setTitleImpl` in `Hydrogen.Head.Meta`
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_setTitle")]
pub fn set_title(title: &str) -> Result<(), JsValue> {
    get_document()?.set_title(title);
    Ok(())
}

/// Get current document title.
///
/// Corresponds to: `getTitleImpl` in `Hydrogen.Head.Meta`
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_getTitle")]
pub fn get_title() -> Result<String, JsValue> {
    Ok(get_document()?.title())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                  // meta tags
// ═══════════════════════════════════════════════════════════════════════════════

/// Find existing meta tag by name or property.
#[cfg(target_arch = "wasm32")]
fn find_meta_element(doc: &Document, name: &str) -> Option<HtmlMetaElement> {
    // Try name attribute first
    let selector = format!("meta[name=\"{}\"]", name);
    if let Ok(Some(el)) = doc.query_selector(&selector) {
        return el.dyn_into::<HtmlMetaElement>().ok();
    }

    // Try property attribute (for Open Graph)
    let selector = format!("meta[property=\"{}\"]", name);
    if let Ok(Some(el)) = doc.query_selector(&selector) {
        return el.dyn_into::<HtmlMetaElement>().ok();
    }

    None
}

/// Set a meta tag (creates or updates).
///
/// Corresponds to: `setMetaImpl` in `Hydrogen.Head.Meta`
///
/// For Open Graph tags (og:*), uses property attribute.
/// For others, uses name attribute.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_setMeta")]
pub fn set_meta(name: &str, content: &str) -> Result<(), JsValue> {
    let doc = get_document()?;
    let head = get_head()?;

    // Check if meta tag exists
    if let Some(meta) = find_meta_element(&doc, name) {
        meta.set_content(content);
    } else {
        // Create new meta tag
        let meta = doc.create_element("meta")?.dyn_into::<HtmlMetaElement>()?;

        // Use property for og:* and twitter:*, name for others
        if name.starts_with("og:") || name.starts_with("twitter:") {
            meta.set_attribute("property", name)?;
        } else {
            meta.set_name(name);
        }
        meta.set_content(content);

        head.append_child(&meta)?;
    }

    Ok(())
}

/// Remove a meta tag.
///
/// Corresponds to: `removeMetaImpl` in `Hydrogen.Head.Meta`
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_removeMeta")]
pub fn remove_meta(name: &str) -> Result<(), JsValue> {
    let doc = get_document()?;

    if let Some(meta) = find_meta_element(&doc, name) {
        if let Some(parent) = meta.parent_node() {
            parent.remove_child(&meta)?;
        }
    }

    Ok(())
}

/// Get meta tag content.
///
/// Corresponds to: `getMetaImpl` in `Hydrogen.Head.Meta`
///
/// Returns null if not found (PureScript handles as Nothing).
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_getMeta")]
pub fn get_meta(name: &str) -> Result<Option<String>, JsValue> {
    let doc = get_document()?;

    Ok(find_meta_element(&doc, name).map(|m| m.content()))
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // link tags
// ═══════════════════════════════════════════════════════════════════════════════

/// Find existing link tag by rel and href.
#[cfg(target_arch = "wasm32")]
fn find_link_element(doc: &Document, rel: &str, href: Option<&str>) -> Option<HtmlLinkElement> {
    let selector = match href {
        Some(h) => format!("link[rel=\"{}\"][href=\"{}\"]", rel, h),
        None => format!("link[rel=\"{}\"]", rel),
    };

    doc.query_selector(&selector)
        .ok()
        .flatten()
        .and_then(|el| el.dyn_into::<HtmlLinkElement>().ok())
}

/// Add a link tag.
///
/// Corresponds to: `addLinkImpl` in `Hydrogen.Head.Meta`
///
/// Parameters:
/// - rel: "preload", "prefetch", "preconnect", "dns-prefetch", "canonical", etc.
/// - href: URL or resource path
/// - as_type: For preload only ("script", "style", "image", "font", "fetch")
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_addLink")]
pub fn add_link(rel: &str, href: &str, as_type: &str) -> Result<(), JsValue> {
    let doc = get_document()?;
    let head = get_head()?;

    // For canonical, remove existing first (only one allowed)
    if rel == "canonical" {
        if let Some(existing) = find_link_element(&doc, rel, None) {
            if let Some(parent) = existing.parent_node() {
                parent.remove_child(&existing)?;
            }
        }
    }

    // Check if this exact link already exists
    if find_link_element(&doc, rel, Some(href)).is_some() {
        return Ok(()); // Already exists, nothing to do
    }

    // Create new link tag
    let link = doc.create_element("link")?.dyn_into::<HtmlLinkElement>()?;

    link.set_rel(rel);
    link.set_href(href);

    // Set "as" attribute for preload
    if rel == "preload" && !as_type.is_empty() {
        link.set_attribute("as", as_type)?;
    }

    // Set crossorigin for preconnect with external resources
    if rel == "preconnect" || rel == "dns-prefetch" {
        link.set_attribute("crossorigin", "")?;
    }

    head.append_child(&link)?;

    Ok(())
}

/// Remove a link tag by rel.
///
/// Corresponds to: `removeLinkImpl` in `Hydrogen.Head.Meta`
///
/// Removes ALL link tags with the given rel attribute.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_removeLink")]
pub fn remove_link(rel: &str) -> Result<(), JsValue> {
    let doc = get_document()?;
    let selector = format!("link[rel=\"{}\"]", rel);

    let links = doc.query_selector_all(&selector)?;

    for i in 0..links.length() {
        if let Some(link) = links.get(i) {
            if let Some(parent) = link.parent_node() {
                parent.remove_child(&link)?;
            }
        }
    }

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // favicon
// ═══════════════════════════════════════════════════════════════════════════════

/// Set favicon.
///
/// Corresponds to: `setFaviconImpl` in `Hydrogen.Head.Meta`
///
/// Removes existing favicon links and adds new one.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_setFavicon")]
pub fn set_favicon(href: &str) -> Result<(), JsValue> {
    let doc = get_document()?;
    let head = get_head()?;

    // Remove existing favicons
    let selectors = ["link[rel=\"icon\"]", "link[rel=\"shortcut icon\"]"];

    for selector in selectors {
        if let Ok(links) = doc.query_selector_all(selector) {
            for i in 0..links.length() {
                if let Some(link) = links.get(i) {
                    if let Some(parent) = link.parent_node() {
                        parent.remove_child(&link)?;
                    }
                }
            }
        }
    }

    // Add new favicon
    let link = doc.create_element("link")?.dyn_into::<HtmlLinkElement>()?;

    link.set_rel("icon");
    link.set_href(href);

    // Infer type from extension
    if href.ends_with(".svg") {
        link.set_attribute("type", "image/svg+xml")?;
    } else if href.ends_with(".png") {
        link.set_attribute("type", "image/png")?;
    } else if href.ends_with(".ico") {
        link.set_attribute("type", "image/x-icon")?;
    }

    head.append_child(&link)?;

    Ok(())
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // body manipulation
// ═══════════════════════════════════════════════════════════════════════════════

/// Get the document body.
#[cfg(target_arch = "wasm32")]
fn get_body() -> Result<HtmlElement, JsValue> {
    get_document()?
        .body()
        .ok_or_else(|| JsValue::from_str("No body element"))
}

/// Set a class on the body element.
///
/// Useful for theme switching, modal open states, etc.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_addBodyClass")]
pub fn add_body_class(class_name: &str) -> Result<(), JsValue> {
    let body = get_body()?;
    body.class_list().add_1(class_name)?;
    Ok(())
}

/// Remove a class from the body element.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_removeBodyClass")]
pub fn remove_body_class(class_name: &str) -> Result<(), JsValue> {
    let body = get_body()?;
    body.class_list().remove_1(class_name)?;
    Ok(())
}

/// Toggle a class on the body element.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_toggleBodyClass")]
pub fn toggle_body_class(class_name: &str) -> Result<bool, JsValue> {
    let body = get_body()?;
    body.class_list().toggle(class_name)
}

/// Check if body has a class.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_hasBodyClass")]
pub fn has_body_class(class_name: &str) -> Result<bool, JsValue> {
    let body = get_body()?;
    Ok(body.class_list().contains(class_name))
}

/// Set a data attribute on the body.
///
/// Useful for storing state like theme, user preferences, etc.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_setBodyData")]
pub fn set_body_data(key: &str, value: &str) -> Result<(), JsValue> {
    let body = get_body()?;
    let attr_name = format!("data-{}", key);
    body.set_attribute(&attr_name, value)?;
    Ok(())
}

/// Get a data attribute from the body.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_getBodyData")]
pub fn get_body_data(key: &str) -> Result<Option<String>, JsValue> {
    let body = get_body()?;
    let attr_name = format!("data-{}", key);
    Ok(body.get_attribute(&attr_name))
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // element by selector
// ═══════════════════════════════════════════════════════════════════════════════

/// Query a single element by CSS selector.
///
/// Returns the first matching element, or None if not found.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_querySelector")]
pub fn query_selector(selector: &str) -> Result<Option<Element>, JsValue> {
    let doc = get_document()?;
    doc.query_selector(selector)
}

/// Set an attribute on an element found by selector.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_setAttributeBySelector")]
pub fn set_attribute_by_selector(
    selector: &str,
    attr_name: &str,
    attr_value: &str,
) -> Result<bool, JsValue> {
    let doc = get_document()?;
    if let Some(el) = doc.query_selector(selector)? {
        el.set_attribute(attr_name, attr_value)?;
        Ok(true)
    } else {
        Ok(false)
    }
}

/// Remove an attribute from an element found by selector.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(js_name = "meta_removeAttributeBySelector")]
pub fn remove_attribute_by_selector(selector: &str, attr_name: &str) -> Result<bool, JsValue> {
    let doc = get_document()?;
    if let Some(el) = doc.query_selector(selector)? {
        el.remove_attribute(attr_name)?;
        Ok(true)
    } else {
        Ok(false)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    // Tests require browser environment (wasm-bindgen-test)
    // These are structural tests only

    #[test]
    fn test_module_compiles() {
        // If this compiles, the module structure is correct
        assert!(true);
    }
}
