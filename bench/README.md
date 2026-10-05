# Benchmarks

Benchmark programs, vendored unmodified, for `.claude/skills/nm-bench`.
Each file is one self-contained program that defines a global `main()`,
which runs the benchmark and prints `Score (version N): S` (higher is
better).

## `octane/`

The 12 benchmarks of the Octane 2.0 suite (score version 9). Each file
concatenates three parts:

1. Octane's `base.js` (the `BenchmarkSuite` harness);
2. the benchmark;
3. a run harness that defines `PrintResult`/`PrintScore` and `main()`.
   The file's last line calls `main();`. The nm-bench scripts remove that
   line for snapshot flows (see `lib.sh`).

The harness parts are copyright the V8 project authors (BSD 3-clause; see
each file's header). The benchmarks keep their own licenses, which are
stated in each file:

| file | benchmark license |
|---|---|
| box2d.js | Box2D: zlib (Erin Catto); Octane's driver: GPL v2 or later |
| code-load.js | Closure Library: Apache 2.0; Octane's driver: BSD 3-clause |
| crypto.js | Tom Wu's jsbn: MIT-style |
| deltablue.js | GPL v2 or later (John Maloney and Mario Wolczko) |
| earley-boyer.js | scheme2js output, no notice of its own: the header's BSD 3-clause |
| mandreel.js | BSD 3-clause (Onan Games) |
| navier-stokes.js | MIT-style (Oliver Hunt) |
| pdfjs.js | GPL v2 or later (Mozilla Foundation, Google) |
| raytrace.js | MIT-style (includes Prototype 1.5.0) |
| regexp.js | BSD 3-clause (V8 project authors) |
| richards.js | BSD 3-clause (V8 project authors) |
| splay.js | BSD 3-clause (V8 project authors) |

These licenses cover only these files. They do not apply to NightMonkey,
which only reads the files as benchmark input.

## `react/react.js`

A server-side-rendering benchmark: an esbuild bundle of React 19.2.6's
`react`, `react-dom` and `react-dom/server` (MIT, Meta Platforms; the
license notices are at the end of the bundle) plus a harness. The harness
renders a Kanban-board page with `renderToString` repeatedly for 3 seconds
and prints an Octane-style `Score (version 9)`. Its first line replaces
`Math.random` with a seeded generator, so every run renders the same page.
It defines `main()` but does not call it.
