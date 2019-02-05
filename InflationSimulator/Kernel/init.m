(* ::Package:: *)

(* Wolfram Language Init File *)


If[PacletNewerQ[
		"1.0", Lookup[Association[PacletInformation["UsageString"]], "Version", "-1"]],
	With[{usageStringURL = "https://github.com/maxitg/UsageString/releases/download/" <>
			"1.0/UsageString-1.0.paclet"},
		If[ChoiceDialog[
				"UsageString needs to be installed in order to use InflationSimulator." <>
				" Install now?"],
			PacletInstall[usageStringURL];
		]
	]
]


Get["InflationSimulator`InflationSimulator`"]
