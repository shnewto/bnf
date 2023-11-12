# Release Process

- leave the Cargo.toml package version alone :)
- trigger the `tag and publish crate [manual]` action and specify the release increment (major, minor, or patch)
  - once the action completes, the Cargo.toml will be updated and the crate will be live on crates.io
- create a release (with title, notes, thanks, etc) and tie it to the tag that was created by the action / new crate version

## Execution

The order of operations for tagging and publishing in the action is this

1. run all checks, i.e. fmt, clippy, tests, etc
1. push change / update to the Cargo.toml
1. push the new tag to the repo
1. publish the new version to crates.io

## Troubleshooting

- if step 1 of execution fails, after addressing the error, you run the action again
- if step 2 of execution fails, after addressing the error, you run the action again
- if step 3 of execution fails (the Cargo.toml version was incremented), after addressing the error, you should manually tag (github's ux or the cli) and manually publish the crate with `cargo publish`
- if step 4 of execution fails (the Cargo.toml version was incremented and there's a new corresponding tag), after addressing the error, you should manually publish the crate  with `cargo publish`
