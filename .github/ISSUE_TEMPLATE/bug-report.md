---
name: Bug Report
about: Create a report to help us improve
title: "[BUG]"
labels: ''
assignees: ''

---

**Describe the bug**
A clear and concise description of where and what the bug is.
- Is the problem in the behavior of the library, an executable we supplied, a test case you wrote, the docs, etc.?
- Is it a math error? A communication error? A design error?

**To Reproduce**
Steps to reproduce the behavior:
1. Optionally create a Rust file in `src/bin` or `tests` [not necessary if the problem is with one of our binaries]
2. Run the following `cargo` command: '....'
3. Scroll down to '....'
4. See error

**Expected behavior**
A clear and concise description of what you expected to happen.

**Screenshots**
If applicable, cut and paste the bad output here to help explain your problem.

**Desktop (please complete the following information):**
 - OS: [e.g. iOS]
 - Version [e.g. 22]
 - Rust version: [e.g. rustc 1.77.2 (25ef9e3d8 2024-04-09)]

You can get this information from:
   `cargo -V ; cargo  pkgid --verbose ; cargo  rustc --quiet -- --print sysroot ; cargo  rustc --quiet -- -V ; uname -a`

**Additional context**
Add any other context about the problem here.
