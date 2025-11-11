# Cutting a new release of `Wac`

To cut a new release, you will need to do the following:

1. Confirm that [CI is green](https://github.com/bytecodealliance/wac/actions) for the commit selected to be tagged and released.

2. Change the workspace version number in [Cargo.toml](./Cargo.toml) and the versions for the crates in the workspace dependencies (e.g. `wac-parser`). Additionally change the version in the result `wat` files that include a `producers` section. E.g.:
``` (@producers (processed-by "wac-parser" "0.8.0"))```

3. Create a pull request with these changes and merge once approved.

4. Checkout the commit with the version bump from above.

5. Create and push a new tag with a `v` and then the version number.

    As an example, via the `git` CLI:

    ```
    # Create a GPG-signed and annotated tag
    git tag -s -m "Wac v0.8.0" v0.8.0

    # Push the tag to the remote corresponding to bytecodealliance/wac (here 'origin')
    git push origin v0.8.0
    ```

6. Pushing the tag upstream will trigger the release actions which creates a release and publishes the crates in this workspace to `crates.io`