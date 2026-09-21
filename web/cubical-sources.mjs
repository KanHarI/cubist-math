// Native path proofs use interval computation; the Id/J edition remains
// available for the explicit legacy backend. The UI shows the actual file.
export const cubicalSourceFiles = Object.freeze({
  circle_degree: "cubical/circle_degree.proof",
  permutations: "cubical/permutations.proof",
  binomial_pascal: "cubical/binomial_pascal.proof",
  kernel_quotient_image: "cubical/kernel_quotient_image.proof",
  field_extensions: "cubical/field_extensions.proof",
  group_univalence: "cubical/group_univalence.proof",
  bouquet_generation: "cubical/bouquet_generation.proof",
  bouquet_cover: "cubical/bouquet_cover.proof",
  bouquet_actions: "cubical/bouquet_actions.proof",
  bijection_equality: "cubical/bijection_equality.proof",
  circle: "cubical/circle.proof",
  equivalence_from_inverse: "cubical/equivalence_from_inverse.proof",
  field_extensionality: "cubical/field_extensionality.proof",
  field_products: "cubical/field_products.proof",
  galois_paths: "cubical/galois_paths.proof",
  group_total_identity: "cubical/group_total_identity.proof",
  homotopy_paths: "cubical/homotopy_paths.proof",
  identity_systems: "cubical/identity_systems.proof",
  normal_subgroups: "cubical/normal_subgroups.proof",
  path_actions: "cubical/path_actions.proof",
  paths: "cubical/paths.proof",
  structured_sets: "cubical/structured_sets.proof",
  subdivision_transport: "cubical/subdivision_transport.proof",
  subfield_transport: "cubical/subfield_transport.proof",
});
export const cubicalSourceFile = name => cubicalSourceFiles[name] ?? `${name}.proof`;
