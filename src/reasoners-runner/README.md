# reasoners-runner


This is a support tool to run some Existential rule engines such as VLog, DLV, and DLV-E.
VLog is not needed to run this tool, but the dlv and dlvExists binaries, named "dlv" and "dlvExists", respectively, are required in the same directory of the jar of reasoners-runner.

## How to build
To build this project you need first to build the warded-rewriter project and install it in your local Maven repository:

- Inside thw warded-rewriter directory type:
    - `mvn compile assembly:single`
    - `mvn install`
- Inside this directory type:
    - `mvn compile assembly:single`
