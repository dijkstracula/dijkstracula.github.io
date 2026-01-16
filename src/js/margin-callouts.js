// Handle margin callout positioning on small screens
(function() {
  const BREAKPOINT = 1200; // Match the CSS media query breakpoint

  // Store original positions for restoration
  const originalPositions = new Map();
  let lastScreenState = null; // Track whether we were last on small or large screen

  function initializePositions() {
    // Store original positions on first run
    const callouts = document.querySelectorAll('.callout-margin');
    callouts.forEach(callout => {
      if (!originalPositions.has(callout)) {
        const nextElement = callout.nextElementSibling;
        if (nextElement) {
          originalPositions.set(callout, nextElement);
        }
      }
    });
  }

  function handleMarginCallouts() {
    const callouts = document.querySelectorAll('.callout-margin');
    const isSmallScreen = window.innerWidth <= BREAKPOINT;

    // Only do work if screen state changed
    if (lastScreenState === isSmallScreen && lastScreenState !== null) {
      return;
    }
    lastScreenState = isSmallScreen;

    callouts.forEach(callout => {
      const originalNext = originalPositions.get(callout);
      if (!originalNext) return;

      if (isSmallScreen) {
        // On small screens, move callout after the next element (if not already there)
        if (callout.nextElementSibling === originalNext) {
          // Move callout after the original next element
          if (originalNext.nextSibling) {
            originalNext.parentNode.insertBefore(callout, originalNext.nextSibling);
          } else {
            originalNext.parentNode.appendChild(callout);
          }
        }
      } else {
        // On large screens, restore to original position (before originalNext)
        if (callout.nextElementSibling !== originalNext) {
          originalNext.parentNode.insertBefore(callout, originalNext);
        }
      }
    });
  }

  // Run on load
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', function() {
      initializePositions();
      handleMarginCallouts();
    });
  } else {
    initializePositions();
    handleMarginCallouts();
  }

  // Run on resize (debounced)
  let resizeTimer;
  window.addEventListener('resize', function() {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(handleMarginCallouts, 250);
  });
})();
