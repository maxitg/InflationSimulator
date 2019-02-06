(* ::Package:: *)

(* ::Title:: *)
(*Inflation Simulator*)


(* ::Section:: *)
(*Begin*)


(* ::Text:: *)
(*See on GitHub: https://github.com/maxitg/InflationSimulator.*)


BeginPackage["InflationSimulator`", {"UsageString`"}];


InflationSimulator`Private`$PublicSymbols = {
	InflatonDensity, InflatonPressure, InflationEquationsOfMotion};


Unprotect @@ InflationSimulator`Private`$PublicSymbols;
ClearAll @@ InflationSimulator`Private`$PublicSymbols;


(* ::Section:: *)
(*Implementation*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Density*)


InflatonDensity::usage = UsageString[
	"InflatonDensity[`\[ScriptCapitalL]`, \!\(\*SubscriptBox[\(`\[CurlyPhi]`\), \(`t`\)]\)] yields the density ",
	"of the field with Lagrangian `\[ScriptCapitalL]` and time derivative of the field ",
	"\!\(\*SubscriptBox[\(`\[CurlyPhi]`\), \(`t`\)]\), assuming homogeneity and isotropy."
];


InflatonDensity[lagrangian_, fieldDerivative_] :=
	-lagrangian + D[lagrangian, fieldDerivative] fieldDerivative


(* ::Subsection:: *)
(*Pressure*)


InflatonPressure::usage = UsageString[
	"InflatonPressure[`\[ScriptCapitalL]`, \!\(\*SubscriptBox[\(`\[CurlyPhi]`\), \(`t`\)]\)] yields the ",
	"pressure of the field with Lagrangian `\[ScriptCapitalL]` and time derivative of the field ",
	"\!\(\*SubscriptBox[\(`\[CurlyPhi]`\), \(`t`\)]\), assuming homogeneity and isotropy."
];


InflatonPressure[lagrangian_, fieldDerivative_] := lagrangian


(* ::Subsection:: *)
(*Equations of Motion*)


InflationEquationsOfMotion::usage = UsageString[
	"InflationEquationsOfMotion[`\[ScriptCapitalL]`, `\[CurlyPhi][t]`, `n[t]`, `t`] yields Euler-Lagrange ",
	"and Friedmann equations fully describing the evolution of a field `\[CurlyPhi]` with ",
	"Lagrangian `\[ScriptCapitalL]` in homogeneous and isotropic spacetime, ",
	"where the number of e-foldings is `n`."
];


ClearAll[$EulerLagrangeEquation];
$EulerLagrangeEquation[lagrangian_, field_, efoldings_, time_] := (
	D[lagrangian, field] - 3 D[efoldings, time] D[lagrangian, D[field, time]]
			- D[lagrangian, D[field, time], time] == 0)


ClearAll[$FriedmannEquation];
$FriedmannEquation[lagrangian_, field_, efoldings_, time_] :=
	D[efoldings, time] == Sqrt[1/3 InflatonDensity[lagrangian, D[field, time]]]


InflationEquationsOfMotion[args___] :=
	{$EulerLagrangeEquation[args], $FriedmannEquation[args]}


(* ::Section:: *)
(*End*)


Protect @@ InflationSimulator`Private`$PublicSymbols;


End[];


EndPackage[];
