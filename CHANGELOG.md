# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning. Before 1.0, a minor version closes a milestone of `docs/spec/14-milestones.md` and a patch version is a step inside a milestone.

## [Unreleased]

### Added

- The `rulean` command line with `help` and `version`. The other commands of the spec exit with code 2 and name the milestone that adds them.
- The exit codes of spec section 09.3.
- CI on Linux (x86-64 and ARM), macOS and Windows, CodeQL, OpenSSF Scorecard, zizmor and Dependabot.
- A release workflow that builds the binaries, writes SHA-256 checksums and signs build provenance attestations.
- The specification in `docs/spec/`.
