# Decaf with λ-expressions

Decaf is a small Java-like language for education purpose. This repository implements new features of λ-expressions, based on the original branch. Apart from MIPS-backend, it also compiles to JVM.

## Getting Started

To build this project, you need JDK 14 (NOTE: the original branch was developed under JDK 12).

Other dependencies will be automatically downloaded from the maven central repository by the build script.

## Build

Type standard [sbt](https://www.scala-sbt.org) commands after you launch the REPL with `sbt`.

To compile, type:

```
sbt:decaf-in-scala> compile
```

To build a standalone jar, type:

```
sbt:decaf-in-scala> assembly
```

To start a scala REPL, type:

```
sbt:decaf-in-scala> console
```

Or, import the project in IDEA and use sbt plugin, if available.

## Run

In sbt console, type:

```
sbt:decaf-in-scala> run --help
```

to show the usage help. Or you first build a standalone jar and run it in CLI.

Possible targets/tasks are:

- PA1: parse source code and output the pretty printed tree, or error messages
- PA2: type check and output the pretty printed scopes, or error messages
- PA3: generate TAC (three-address code), dump it to a .tac file, and then output the execution result using our built-in simulator
- PA3-JVM: generate JVM bytecode
- PA4: currently same with PA3, will be reserved for students to do a bunch of optimizations on TAC
- PA5: (default target) allocate registers and emit assembly code, currently we are using a very brute-force algorithm and only generates MIPS assembly code (with pseudo-ops, and no delayed branches)

To run the MIPS assembly code, you may need [spim](http://spimsimulator.sourceforge.net), a MIPS32 simulator.
For Mac OS users, simply install `spim` with `brew install spim` and run with `spim -file your_file.s`.

## Demo

The `demo/` folder contains a little testcase with new features. For example, to compile this to JVM:

```
cd demo/
mkdir out/
java -jar ../target/decaf.jar demo/demo.decaf -t PA3-JVM -d out
cd out/
java Main
```

You may use Java disassembly tools to inspect the bytecode generated for this testcase, e.g.

```
javap -v -p Foo
javap -v -p Main
```

## Test

For more testcases with the new λ-expression feature, see [here](https://github.com/decaf-lang/decaf-2019-tests).