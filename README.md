# Inflation Simulator
Code for simulating inflation, including Lagrangians with non-canonical kinetic energy.

## Build

1. Open the project in Wolfram Workbench using File -> Open Projects from File System..., and selecting root repository directory.
2. Open Window -> Show View -> Application Tools.
3. Select `InflationSimulator` as a project.
4. Click Build to build documentation.
5. Click Deploy Application, and select a directory to put a temporary deployed package.
6. Make sure all files selected, click Next. Make sure documentation is selected, click Finish. A new directory `InflationSimulator` will be created in a directory specified.
7. Open Mathematica, and evaluate ```PacletManager`PackPaclet["path_to_newly_created_UsageString_directory"]```. The output will be the path to the compiled paclet.

## Install

Evaluate ```PacletManager`PacletInstall["path_to_paclet"]```, where `path_to_paclet` is the path to the `.paclet` file, which can either be downloaded from releases page, or build using the steps above.