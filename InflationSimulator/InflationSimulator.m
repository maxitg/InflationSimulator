(* ::Package:: *)

(* ::Title:: *)
(*Inflation Simulator*)


(* ::Section:: *)
(*Begin*)


(* ::Text:: *)
(*See on GitHub: https://github.com/maxitg/InflationSimulator.*)


BeginPackage["InflationSimulator`", {"UsageString`"}]


InflationSimulator`$PublicSymbols = {FieldDensity, FieldPressure};


Unprotect @@ InflationSimulator`Private`$PublicSymbols;
ClearAll @@ InflationSimulator`Private`$PublicSymbols;


(* ::Section:: *)
(*Implementation*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Field Density*)


FieldDensity::usage = UsageString[
	"FieldDensity[`\[ScriptCapitalL]`, \!\(\*SubscriptBox[\(`\[CurlyPhi]`\), \(`t`\)]\)] yields the density ",
	"of the field with Lagrangian `\[ScriptCapitalL]` and time derivative of the field ",
	"\!\(\*SubscriptBox[\(`\[CurlyPhi]`\), \(`t`\)]\)."
];


FieldDensity[\[ScriptCapitalL]_, \[CurlyPhi]d_] := -\[ScriptCapitalL] + \!\(
\*SubscriptBox[\(\[PartialD]\), \(\[CurlyPhi]d\)]\[ScriptCapitalL]\) \[CurlyPhi]d


(* ::Subsection:: *)
(*Field Pressure*)


FieldPressure::usage = UsageString[
	"FieldPressure[`\[ScriptCapitalL]`, \!\(\*SubscriptBox[\(`\[CurlyPhi]`\), \(`t`\)]\)] yields the pressure ",
	"of the field with Lagrangian `\[ScriptCapitalL]` and time derivative of the field ",
	"\!\(\*SubscriptBox[\(`\[CurlyPhi]`\), \(`t`\)]\)."
];


FieldPressure[\[ScriptCapitalL]_, \[CurlyPhi]d_] := \[ScriptCapitalL]


(* ::Section:: *)
(*End*)


Protect @@ InflationSimulator`Private`$PublicSymbols;


End[];


EndPackage[];
