// FFI for Hydrogen.Chart.PieChart
// SVG pie chart animations and interactions

export const animateSlicesImpl = chartId => duration => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return;
  // Animate slice entry
  const slices = chart.querySelectorAll('.pie-slice');
  slices.forEach((slice, i) => {
    slice.style.transition = `transform ${duration}ms ease-out`;
    slice.style.transform = 'scale(1)';
  });
};

export const animateSlicesRotateImpl = chartId => angle => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return;
  const slices = chart.querySelector('.pie-slices');
  if (slices) {
    slices.style.transform = `rotate(${angle}deg)`;
  }
};

export const resetSlicesImpl = chartId => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return;
  const slices = chart.querySelector('.pie-slices');
  if (slices) {
    slices.style.transform = 'rotate(0deg)';
  }
};

export const explodeSliceImpl = chartId => index => distance => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return;
  const slice = chart.querySelectorAll('.pie-slice')[index];
  if (slice) {
    // Calculate direction from center based on slice angle
    const angle = parseFloat(slice.dataset.midAngle || 0);
    const rad = angle * Math.PI / 180;
    const dx = Math.cos(rad) * distance;
    const dy = Math.sin(rad) * distance;
    slice.style.transform = `translate(${dx}px, ${dy}px)`;
  }
};

export const resetExplodeImpl = chartId => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return;
  const slices = chart.querySelectorAll('.pie-slice');
  slices.forEach(slice => {
    slice.style.transform = 'translate(0, 0)';
  });
};

export const initExplodeOnClickImpl = chartId => distance => callback => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return () => {};
  
  const handler = (e) => {
    const slice = e.target.closest('.pie-slice');
    if (slice) {
      const index = parseInt(slice.dataset.index || 0, 10);
      callback(index)();
    }
  };
  
  chart.addEventListener('click', handler);
  return () => chart.removeEventListener('click', handler);
};

export const initTooltipsImpl = chartId => sliceData => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return () => {};
  
  let tooltip = document.createElement('div');
  tooltip.className = 'pie-tooltip';
  tooltip.style.cssText = 'position:absolute;display:none;background:#333;color:#fff;padding:4px 8px;border-radius:4px;pointer-events:none;z-index:1000';
  chart.appendChild(tooltip);
  
  const show = (e) => {
    const slice = e.target.closest('.pie-slice');
    if (slice) {
      const index = parseInt(slice.dataset.index || 0, 10);
      const data = sliceData[index];
      if (data) {
        tooltip.textContent = `${data.label}: ${data.value}`;
        tooltip.style.display = 'block';
        tooltip.style.left = e.offsetX + 10 + 'px';
        tooltip.style.top = e.offsetY + 10 + 'px';
      }
    }
  };
  
  const hide = () => {
    tooltip.style.display = 'none';
  };
  
  chart.addEventListener('mousemove', show);
  chart.addEventListener('mouseleave', hide);
  
  return () => {
    chart.removeEventListener('mousemove', show);
    chart.removeEventListener('mouseleave', hide);
    tooltip.remove();
  };
};

export const highlightSliceImpl = chartId => index => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return;
  const slice = chart.querySelectorAll('.pie-slice')[index];
  if (slice) {
    slice.classList.add('highlighted');
  }
};

export const clearHighlightsImpl = chartId => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return;
  const slices = chart.querySelectorAll('.pie-slice.highlighted');
  slices.forEach(slice => slice.classList.remove('highlighted'));
};

export const initHoverEffectsImpl = chartId => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return () => {};
  
  const enter = (e) => {
    const slice = e.target.closest('.pie-slice');
    if (slice) {
      slice.style.filter = 'brightness(1.1)';
    }
  };
  
  const leave = (e) => {
    const slice = e.target.closest('.pie-slice');
    if (slice) {
      slice.style.filter = '';
    }
  };
  
  chart.addEventListener('mouseenter', enter, true);
  chart.addEventListener('mouseleave', leave, true);
  
  return () => {
    chart.removeEventListener('mouseenter', enter, true);
    chart.removeEventListener('mouseleave', leave, true);
  };
};

export const getAngleFromMouseImpl = chartId => x => y => () => {
  const chart = document.getElementById(chartId);
  if (!chart) return 0;
  const rect = chart.getBoundingClientRect();
  const cx = rect.width / 2;
  const cy = rect.height / 2;
  const dx = x - rect.left - cx;
  const dy = y - rect.top - cy;
  return Math.atan2(dy, dx) * 180 / Math.PI;
};
