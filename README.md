`egg` Tactic: E-Graphs in Lean
===============================

This repository contains work-in-progress of a [Lean4](https://leanprover.github.io/) tactic to prove equalities, powered by E-Graphs and the [egg](https://egraphs-good.github.io/) project.

# Requirements

To use this tactic you will need a recent version of Lean4, ideally a nightly (see [here](https://leanprover.github.io/lean4/doc/quickstart.html) for installation instructions.

You will also need an installation of [Rust](https://www.rust-lang.org/learn/get-started) to compile the egg integration.

# Building

To build this, just run the following in the `json-egg` directory:
```
 cargo build --release
 ```

# Using 

Just open the `EggTactic/Test.lean` file in your favorite editor that supports Lean4 and you should be able to use the `rawEgg` tactic to prove your equalities. We have not yet packaged this to use directly in your own project.

# Work in progress

This project is work in progress and is not yet ready for everyday use. Don't worry however, you won't be able to prove anything incorrect with this. In the worst case, the tactic will fail when it shouldn't.

    
