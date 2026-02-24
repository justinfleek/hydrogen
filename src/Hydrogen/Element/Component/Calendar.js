// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                          // hydrogen // element // calendar
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Calendar FFI for date operations
// This is a pure system boundary — date math requires JavaScript's Date API

/**
 * Get the number of days in a month
 * @param {number} year
 * @param {number} month - 1-indexed (1 = January)
 * @returns {number}
 */
export const getDaysInMonthImpl = (year) => (month) => {
  // Day 0 of next month = last day of this month
  return new Date(year, month, 0).getDate();
};

/**
 * Get the day of week for the first day of a month
 * @param {number} year
 * @param {number} month - 1-indexed (1 = January)
 * @returns {number} 0 = Sunday, 6 = Saturday
 */
export const getFirstDayOfMonthImpl = (year) => (month) => {
  return new Date(year, month - 1, 1).getDay();
};

/**
 * Compare two dates
 * @param {object} a - { year, month, day }
 * @param {object} b - { year, month, day }
 * @returns {number} -1 if a < b, 0 if equal, 1 if a > b
 */
export const compareDatesImpl = (a) => (b) => {
  const dateA = new Date(a.year, a.month - 1, a.day);
  const dateB = new Date(b.year, b.month - 1, b.day);
  
  if (dateA < dateB) return -1;
  if (dateA > dateB) return 1;
  return 0;
};

/**
 * Check if two dates are the same
 * @param {object} a - { year, month, day }
 * @param {object} b - { year, month, day }
 * @returns {boolean}
 */
export const sameDateImpl = (a) => (b) => {
  return a.year === b.year && a.month === b.month && a.day === b.day;
};

/**
 * Add days to a date
 * @param {object} date - { year, month, day }
 * @param {number} days - Number of days to add (can be negative)
 * @returns {object} - { year, month, day }
 */
export const addDaysImpl = (date) => (days) => {
  const d = new Date(date.year, date.month - 1, date.day);
  d.setDate(d.getDate() + days);
  return {
    year: d.getFullYear(),
    month: d.getMonth() + 1,
    day: d.getDate()
  };
};

/**
 * Add months to a date
 * Handles month overflow (e.g., Jan 31 + 1 month -> Feb 28/29)
 * @param {object} date - { year, month, day }
 * @param {number} months - Number of months to add (can be negative)
 * @returns {object} - { year, month, day }
 */
export const addMonthsImpl = (date) => (months) => {
  const d = new Date(date.year, date.month - 1 + months, date.day);
  // Handle month overflow (e.g., Jan 31 + 1 month)
  const targetMonth = (date.month - 1 + months) % 12;
  const normalizedTarget = targetMonth >= 0 ? targetMonth : targetMonth + 12;
  if (d.getMonth() !== normalizedTarget) {
    d.setDate(0); // Go to last day of previous month
  }
  return {
    year: d.getFullYear(),
    month: d.getMonth() + 1,
    day: d.getDate()
  };
};

/**
 * Get ISO 8601 week number
 * @param {object} date - { year, month, day }
 * @returns {number} - Week number (1-53)
 */
export const getWeekNumberImpl = (date) => {
  const d = new Date(date.year, date.month - 1, date.day);
  d.setHours(0, 0, 0, 0);
  d.setDate(d.getDate() + 4 - (d.getDay() || 7));
  const yearStart = new Date(d.getFullYear(), 0, 1);
  return Math.ceil((((d - yearStart) / 86400000) + 1) / 7);
};

/**
 * Check if a year is a leap year
 * @param {number} year
 * @returns {boolean}
 */
export const isLeapYearImpl = (year) => {
  return (year % 4 === 0 && year % 100 !== 0) || (year % 400 === 0);
};
