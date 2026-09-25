// Wall-clock budgets in tests bound checks that must succeed, or stop runs
// that hang; they do not measure speed. Shared CI runners are slower and
// noisier than a development machine, so the budgets are scaled there.
// Tests that expect a time limit to be reached must not use this.
//   CUBIST_TEST_TIME_SCALE=<factor> overrides the default factor.
const configured = Number(process.env.CUBIST_TEST_TIME_SCALE);
export const timeScale = Number.isFinite(configured) && configured > 0 ? configured : process.env.CI ? 4 : 1;
export const budget = milliseconds => Math.round(milliseconds * timeScale);
