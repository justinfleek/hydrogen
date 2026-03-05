// FFI for Hydrogen.Playwright
// Playwright browser automation (Node.js only - stubs for browser compilation)

// These are all stubs - Playwright only works in Node.js, not in the browser.
// Canvas app doesn't use Playwright, but Hydrogen exports it.

const notInBrowser = name => () => {
  throw new Error(`Playwright.${name}: Only available in Node.js`);
};

// Browser launch
export const launchBrowserImpl = notInBrowser('launchBrowser');
export const launchImpl = notInBrowser('launch');
export const launchPersistentContextImpl = notInBrowser('launchPersistentContext');
export const closeImpl = notInBrowser('close');

// Context
export const newContextImpl = notInBrowser('newContext');

// Page
export const newPageImpl = notInBrowser('newPage');
export const gotoImpl = notInBrowser('goto');
export const reloadImpl = notInBrowser('reload');
export const goBackImpl = notInBrowser('goBack');
export const goForwardImpl = notInBrowser('goForward');
export const urlImpl = notInBrowser('url');
export const titleImpl = notInBrowser('title');
export const contentImpl = notInBrowser('content');
export const setContentImpl = notInBrowser('setContent');

// Locators
export const locatorImpl = notInBrowser('locator');
export const getByTextImpl = notInBrowser('getByText');
export const getByRoleImpl = notInBrowser('getByRole');
export const getByLabelImpl = notInBrowser('getByLabel');
export const getByPlaceholderImpl = notInBrowser('getByPlaceholder');
export const getByTestIdImpl = notInBrowser('getByTestId');
export const firstImpl = notInBrowser('first');
export const lastImpl = notInBrowser('last');
export const nthImpl = notInBrowser('nth');
export const countImpl = notInBrowser('count');

// Actions
export const clickImpl = notInBrowser('click');
export const dblclickImpl = notInBrowser('dblclick');
export const fillImpl = notInBrowser('fill');
export const typeImpl = notInBrowser('type');
export const pressImpl = notInBrowser('press');
export const checkImpl = notInBrowser('check');
export const uncheckImpl = notInBrowser('uncheck');
export const selectOptionImpl = notInBrowser('selectOption');
export const hoverImpl = notInBrowser('hover');
export const focusImpl = notInBrowser('focus');
export const blurImpl = notInBrowser('blur');

// Queries
export const textContentImpl = notInBrowser('textContent');
export const innerTextImpl = notInBrowser('innerText');
export const innerHTMLImpl = notInBrowser('innerHTML');
export const inputValueImpl = notInBrowser('inputValue');
export const getAttributeImpl = notInBrowser('getAttribute');
export const isVisibleImpl = notInBrowser('isVisible');
export const isHiddenImpl = notInBrowser('isHidden');
export const isEnabledImpl = notInBrowser('isEnabled');
export const isDisabledImpl = notInBrowser('isDisabled');
export const isCheckedImpl = notInBrowser('isChecked');

// Waits
export const waitForSelectorImpl = notInBrowser('waitForSelector');
export const waitForURLImpl = notInBrowser('waitForURL');
export const waitForLoadStateImpl = notInBrowser('waitForLoadState');
export const waitForFunctionImpl = notInBrowser('waitForFunction');
export const waitForTimeoutImpl = notInBrowser('waitForTimeout');

// Evaluate
export const evaluateImpl = notInBrowser('evaluate');
export const evaluateHandleImpl = notInBrowser('evaluateHandle');

// Screenshots/PDF
export const screenshotImpl = notInBrowser('screenshot');
export const screenshotElementImpl = notInBrowser('screenshotElement');
export const pdfImpl = notInBrowser('pdf');
