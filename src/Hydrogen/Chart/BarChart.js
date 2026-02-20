// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // barchart
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Bar Chart animation and interactivity FFI

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // animation
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Animate bars from zero to their target height
 * @param {string} containerId - Container element ID
 * @param {number} duration - Animation duration in ms
 */
export const animateBarsImpl = (containerId) => (duration) => () => {
  const container = document.getElementById(containerId);
  if (!container) return;

  const bars = container.querySelectorAll('rect[data-animate="true"]');
  
  bars.forEach((bar, index) => {
    const targetHeight = parseFloat(bar.getAttribute('data-target-height'));
    const targetY = parseFloat(bar.getAttribute('data-target-y'));
    const baseY = parseFloat(bar.getAttribute('data-base-y'));
    
    // Start from zero height at base
    bar.setAttribute('height', '0');
    bar.setAttribute('y', String(baseY));
    
    // Animate with delay based on index
    const delay = index * 50;
    
    setTimeout(() => {
      bar.style.transition = `height ${duration}ms ease-out, y ${duration}ms ease-out`;
      bar.setAttribute('height', String(targetHeight));
      bar.setAttribute('y', String(targetY));
    }, delay);
  });
};

/**
 * Reset bar animation
 * @param {string} containerId - Container element ID
 */
export const resetBarsImpl = (containerId) => () => {
  const container = document.getElementById(containerId);
  if (!container) return;

  const bars = container.querySelectorAll('rect[data-animate="true"]');
  
  bars.forEach((bar) => {
    const baseY = parseFloat(bar.getAttribute('data-base-y'));
    bar.style.transition = 'none';
    bar.setAttribute('height', '0');
    bar.setAttribute('y', String(baseY));
  });
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // tooltips
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Initialize tooltips for bar chart
 * @param {string} containerId - Container element ID
 * @param {function} onHover - Callback when hovering a bar
 */
export const initTooltipsImpl = (containerId) => (onHover) => () => {
  const container = document.getElementById(containerId);
  if (!container) return;

  const barGroups = container.querySelectorAll('.bar-group');
  
  barGroups.forEach((group) => {
    const index = parseInt(group.getAttribute('data-index'), 10);
    
    group.addEventListener('mouseenter', (e) => {
      const rect = group.querySelector('rect');
      if (rect) {
        const bbox = rect.getBoundingClientRect();
        onHover({
          index,
          x: bbox.left + bbox.width / 2,
          y: bbox.top,
          visible: true
        })();
      }
    });
    
    group.addEventListener('mouseleave', () => {
      onHover({
        index,
        x: 0,
        y: 0,
        visible: false
      })();
    });
  });
};

/**
 * Create and show a tooltip
 * @param {string} containerId - Container element ID
 * @param {number} x - X position
 * @param {number} y - Y position
 * @param {string} content - Tooltip content
 */
export const showTooltipImpl = (containerId) => (x) => (y) => (content) => () => {
  let tooltip = document.getElementById(containerId + '-tooltip');
  
  if (!tooltip) {
    tooltip = document.createElement('div');
    tooltip.id = containerId + '-tooltip';
    tooltip.className = 'absolute z-50 px-2 py-1 text-xs bg-popover text-popover-foreground rounded shadow-md border pointer-events-none';
    document.body.appendChild(tooltip);
  }
  
  tooltip.textContent = content;
  tooltip.style.left = `${x}px`;
  tooltip.style.top = `${y - 30}px`;
  tooltip.style.transform = 'translateX(-50%)';
  tooltip.style.opacity = '1';
  tooltip.style.visibility = 'visible';
};

/**
 * Hide tooltip
 * @param {string} containerId - Container element ID
 */
export const hideTooltipImpl = (containerId) => () => {
  const tooltip = document.getElementById(containerId + '-tooltip');
  if (tooltip) {
    tooltip.style.opacity = '0';
    tooltip.style.visibility = 'hidden';
  }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                 // hover effects
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Highlight a specific bar
 * @param {string} containerId - Container element ID
 * @param {number} index - Bar index to highlight
 */
export const highlightBarImpl = (containerId) => (index) => () => {
  const container = document.getElementById(containerId);
  if (!container) return;

  const barGroups = container.querySelectorAll('.bar-group');
  
  barGroups.forEach((group, i) => {
    const rect = group.querySelector('rect');
    if (rect) {
      if (i === index) {
        rect.style.filter = 'brightness(1.1)';
        rect.style.transform = 'scaleY(1.02)';
        rect.style.transformOrigin = 'bottom';
      } else {
        rect.style.opacity = '0.5';
      }
    }
  });
};

/**
 * Clear all bar highlights
 * @param {string} containerId - Container element ID
 */
export const clearHighlightsImpl = (containerId) => () => {
  const container = document.getElementById(containerId);
  if (!container) return;

  const barGroups = container.querySelectorAll('.bar-group');
  
  barGroups.forEach((group) => {
    const rect = group.querySelector('rect');
    if (rect) {
      rect.style.filter = '';
      rect.style.transform = '';
      rect.style.opacity = '';
    }
  });
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // responsive
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Get container dimensions
 * @param {string} containerId - Container element ID
 * @returns {{ width: number, height: number }}
 */
export const getContainerSizeImpl = (containerId) => () => {
  const container = document.getElementById(containerId);
  if (!container) return { width: 0, height: 0 };
  
  const rect = container.getBoundingClientRect();
  return {
    width: rect.width,
    height: rect.height
  };
};

/**
 * Set up resize observer
 * @param {string} containerId - Container element ID
 * @param {function} onResize - Callback when container resizes
 * @returns {function} - Cleanup function
 */
export const observeResizeImpl = (containerId) => (onResize) => () => {
  const container = document.getElementById(containerId);
  if (!container) return () => {};

  const observer = new ResizeObserver((entries) => {
    for (const entry of entries) {
      const { width, height } = entry.contentRect;
      onResize({ width, height })();
    }
  });
  
  observer.observe(container);
  
  return () => observer.disconnect();
};
