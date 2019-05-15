# Inflation Simulator
Code for simulating inflation, including multiple field Lagrangians with non-canonical kinetic energy.

## Overview

To demonstrate some functionality of the package, let's consider a two-field potential with a saddle point:

![image](https://user-images.githubusercontent.com/1479325/57750434-df54bf80-76a7-11e9-8264-22665d35739e.png)

![image](https://user-images.githubusercontent.com/1479325/57750380-aa486d00-76a7-11e9-8727-5adcf86461c4.png)

We can obtain equations of motion for this potential by using `InflationEquationsOfMotion`:

![image](https://user-images.githubusercontent.com/1479325/57750454-f5fb1680-76a7-11e9-8a08-db3cfe1586ec.png)

Here `n[t]` stands for the number of e-foldings. We can use these equations to produce an evolution of the fields and the number of e-foldings over time, starting for example with initial conditions `a[0] = 5`, `a'[0] = 0`, `b[0] = 0.2`, `b'[0] = 0` using `InflationEvolution`:

![image](https://user-images.githubusercontent.com/1479325/57750487-1c20b680-76a8-11e9-9785-ee340e8699d9.png)

We get `InterpolatingFunction`s and some extra information such as the total number of e-foldings. If we plot evolution of the fields over time, we can see that the fields reach the saddle point, and "slow-roll" through it for some time:

![image](https://user-images.githubusercontent.com/1479325/57750573-65710600-76a8-11e9-87a1-acc81d7a706b.png)

Let's plot that against the potential to see the trajectory of the fields:

![image](https://user-images.githubusercontent.com/1479325/57750671-bd0f7180-76a8-11e9-862d-89dbe81a79d5.png)

We can check if this particular model is consistent with experimental constraints. One way to do that is to evaluate the ratio of tensor-to-scalar power spectra, and the scalar spectral index, assuming horizon exit for the scale we see today occured 60 e-foldings before the end of inflation:

![image](https://user-images.githubusercontent.com/1479325/57750755-18416400-76a9-11e9-9c36-c78f1730d4d0.png)

Let's check if that's in experimental range:

![image](https://user-images.githubusercontent.com/1479325/57750866-8128dc00-76a9-11e9-8de5-5aae2cba24bf.png)

What if we change the initial value of `b`? Let's plot the scalar spectral index against it:

![image](https://user-images.githubusercontent.com/1479325/57751141-60ad5180-76aa-11e9-8570-93f2f6b6213e.png)

It appears we can get experimentally allowed values near `b[0] = 0.05`. Let's try it:

![image](https://user-images.githubusercontent.com/1479325/57751226-a407c000-76aa-11e9-888a-a75e3d443c44.png)

It is consistent! So, we have found an inflation model (albeit with a non-physical potential) that is consistent with experimental constraints on scalar spectral index and tensor-to-scalar ratio.

## Build

1. Open the project in Wolfram Workbench using File -> Open Projects from File System..., and selecting root repository directory.
2. Open Window -> Show View -> Application Tools.
3. Select `InflationSimulator` as a project.
4. Click Build to build documentation.
5. Click Deploy Application, and select a directory to put a temporary deployed package.
6. Make sure all files selected, click Next. Make sure documentation is selected, click Finish. A new directory `InflationSimulator` will be created in a directory specified.
7. Open Mathematica, and evaluate ```PacletManager`PackPaclet["path_to_newly_created_InflationSimulator_directory"]```. The output will be the path to the compiled paclet.

## Install

Evaluate ```PacletManager`PacletInstall["path_to_paclet"]```, where `path_to_paclet` is the path to the `.paclet` file, which can either be downloaded from releases page, or build using the steps above.
