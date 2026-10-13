// A source control must apply its intended edit. A missing/duplicated site
// is a broken fixture, never a passing copy of the unedited source.
export function editedFixture(source, {anchor, replacement}, id = "fixture") {
  if (!anchor || source.split(anchor).length !== 2)
    throw Error(`${id}: probe anchor must occur exactly once`);
  return source.replace(anchor, replacement);
}
