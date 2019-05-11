(* ::Package:: *)

(* ::Title:: *)
(*Inflation Simulator*)


(* ::Chapter:: *)
(*Begin*)


(* ::Text:: *)
(*See on GitHub: https://github.com/maxitg/InflationSimulator.*)


BeginPackage["InflationSimulator`"];


InflationSimulator`Private`$PublicSymbols = Hold[{
	InflatonDensity, InflatonPressure, InflationEquationsOfMotion,
	InflationEvolution, CosmologicalHorizonExitTime, InflationQ,
	InflationProperty, InflationPropertyData, InflationValue,
	ExperimentallyConsistentInflationQ}];


Unprotect @@@ InflationSimulator`Private`$PublicSymbols;
ClearAll @@@ InflationSimulator`Private`$PublicSymbols;


(* ::Chapter:: *)
(*Implementation*)


Begin["`Private`"];


(* ::Section:: *)
(*Equations of Motion*)


(* ::Subsection:: *)
(*InflatonDensity*)


InflatonDensity::usage = "InflatonDensity[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields the density of a homogeneous field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)] with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\).";


ClearAll[$InflatonDensity];
$InflatonDensity[lagrangian_, fieldsDot_] :=
	-lagrangian + Total[D[lagrangian, #] # & /@ fieldsDot]


InflatonDensity[lagrangian_, fields_List, time_] :=
	$InflatonDensity[lagrangian, D[fields, time]]


InflatonDensity[lagrangian_, field_, time_] :=
	InflatonDensity[lagrangian, {field}, time]


(* ::Subsection:: *)
(*InflatonPressure*)


InflatonPressure::usage = "InflatonPressure[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields the pressure of a homogeneous field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)] with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\).";


InflatonPressure[lagrangian_, fields_, time_] := lagrangian


(* ::Subsection:: *)
(*InflationEquationsOfMotion*)


InflationEquationsOfMotion::usage = "InflationEquationsOfMotion[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"n\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields equations fully describing the evolution of a " <>
"field \!\(\*StyleBox[\"\[CurlyPhi]\", \"TI\"]\) with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\) in homogeneous and isotropic spacetime, where \!\(\*
StyleBox[\"n\", \"TI\"]\) is the number of e-foldings as a function of time \!\(\*
StyleBox[\"t\", \"TI\"]\).";


ClearAll[$FieldSecondTimeDerivative];
$FieldsSecondTimeDerivatives[lagrangian_, fields_, fieldsDot_] := Module[{J, R},
	J = D[lagrangian, {fieldsDot, 2}];
	R = D[lagrangian, {fields}]
		- Sqrt[3 $InflatonDensity[lagrangian, fieldsDot]]
			D[lagrangian, {fieldsDot}]
		- Total[D[lagrangian, {fieldsDot}, #[[1]]] #[[2]] &
			/@ Transpose[{fields, fieldsDot}]];
	Inverse[J].R]


ClearAll[$EfoldingsTimeDerivative];
$EfoldingsTimeDerivative[lagrangian_, fields_, fieldsDot_] :=
	Sqrt[1/3 $InflatonDensity[lagrangian, fieldsDot]]


InflationEquationsOfMotion[lagrangian_, fields_List, efoldings_, time_] := Append[
	Thread[D[fields, {time, 2}] ==
			$FieldsSecondTimeDerivatives[lagrangian, fields, D[fields, time]]],
	D[efoldings, time] ==
			$EfoldingsTimeDerivative[lagrangian, fields, D[fields, time]]]


InflationEquationsOfMotion[lagrangian_, field_, efoldings_, time_] :=
	InflationEquationsOfMotion[lagrangian, {field}, efoldings, time]


(* ::Section:: *)
(*Evolution*)


(* ::Subsection:: *)
(*InflationEvolution*)


(* ::Subsubsection:: *)
(*Usage*)


InflationEvolution::usage = "InflationEvolution[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields functions describing evolution of the field and " <>
"the number of e-foldings as functions of time \!\(\*
StyleBox[\"t\", \"TI\"]\) for a model with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), starting with initial conditions \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\) for the field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\).";


(* ::Subsubsection:: *)
(*Messages*)


InflationEvolution::nnuml =
	"Lagrangian did not evaluate to a numerical value for initial condition.";


(* ::Subsubsection:: *)
(*Options*)


Options[InflationEvolution] = {
	"FinalDensityPrecisionGoal" -> 1.*^-8,
	"FinalDensityRelativeDuration" -> 0.5,
	"ZeroDensityTolerance" -> 10,
	"MaxIntegrationTime" -> \[Infinity]
};


ClearAll[$InitialEfoldings, $InitialDensityFraction, $StoppedEarlyString];
$InitialEfoldings = 0.1;
$InitialDensityFraction = 0.99;
$StoppedEarlyMissing = Missing["Unknown", "Stopped before reaching final density."];


(* ::Subsubsection:: *)
(*Implementation*)


InflationEvolution[
		lagrangian_,
		initialConditions_,
		time_,
		o : OptionsPattern[]] := Module[{
			fields, momenta, lagrangianMomentumSpace, density,
			initialLagrangian, initialDensity, tEnd,
			finalDensitySign, solution, integrationTime,
			field, momentum, efoldings, finalDensity, finalDensityStartTime,
			i},
	{fields, momenta} = Transpose @ Table[
		#[i][time] & /@ {field, momentum}, {i, initialConditions[[All, 1]]}];
	
	lagrangianMomentumSpace = lagrangian /. Flatten @ Table[
		{i'[time] -> momentum[i][time], i[time] -> field[i][time]},
		{i, initialConditions[[All, 1]]}];
	density = $InflatonDensity[lagrangianMomentumSpace, momenta];
	
	{initialLagrangian, initialDensity} =
		{lagrangianMomentumSpace,
		 $InflatonDensity[lagrangianMomentumSpace, momenta]} /. Join[
			Thread[fields -> initialConditions[[All, 2]]],
			Thread[momenta -> initialConditions[[All, 3]]]];
	If[!NumericQ[initialLagrangian],
		Message[InflationEvolution::nnuml]; Return[$Failed]];
	
	tEnd = If[initialDensity <= 0.,
		finalDensitySign = Sign[initialDensity];
		0,
		finalDensitySign = $StoppedEarlyMissing;
		OptionValue["MaxIntegrationTime"]];
	
	solution = With[{
			finalDensityPrecisionGoal = OptionValue["FinalDensityPrecisionGoal"],
			finalDensityRelativeDuration = OptionValue["FinalDensityRelativeDuration"],
			zeroDensityPrecision =
				OptionValue["ZeroDensityTolerance"]
					OptionValue["FinalDensityPrecisionGoal"],
			initialEfoldings = $InitialEfoldings,
			initialDensityFraction = $InitialDensityFraction,
			density = density},
		NDSolve[
			Join[
				(* Initial conditions *)
				Table[field[i[[1]]][0] == i[[2]], {i, initialConditions}],
				Table[momentum[i[[1]]][0] == i[[3]], {i, initialConditions}],
				{efoldings[0] == 0},
				{finalDensity[0] == initialDensity},
				{finalDensityStartTime[0] == 0},
				
				(* Evolution equations *)
				Table[
					field[i]'[time] == momentum[i][time],
					{i, initialConditions[[All, 1]]}],
				Thread[Table[momentum[i]'[time], {i, initialConditions[[All, 1]]}] ==
					(* Re is needed to avoid warnings if negative density is reached,
					   integration is aborted in that case, so no incorrect results
					   are returned. *)
					Re @ $FieldsSecondTimeDerivatives[
						lagrangianMomentumSpace, fields, momenta]],
				{efoldings'[time] == Re @ $EfoldingsTimeDerivative[
					lagrangianMomentumSpace, fields, momenta]},
				
				(* Initialize final density thresholds *)
				{WhenEvent[efoldings[time] >= initialEfoldings ||
						density <= initialDensityFraction initialDensity,
					{finalDensity[time], finalDensityStartTime[time]} ->
						{density, time},
					"LocationMethod" -> "StepEnd"]},
				
				(* Reached time threshold, potential end-of-inflation *)
				{WhenEvent[time > finalDensityStartTime[time] /
						(1 - finalDensityRelativeDuration),
					If[finalDensity[time] - density <=
							finalDensityPrecisionGoal
								(initialDensity - finalDensity[time]),
						(* density is stable, check sign and stop *)
						finalDensitySign = If[
							density <= zeroDensityPrecision initialDensity,
							0,
							+1];
						"StopIntegration",
						(* density is still changing, set new threshold *)
						{finalDensity[time], finalDensityStartTime[time]} ->
							{density, time}],
					"LocationMethod" -> "StepEnd"]},
				 
				(* Reached negative density, abort *)
				{WhenEvent[density < 0,
					finalDensitySign = -1;
					"StopIntegration",
					"LocationMethod" -> "StepEnd"]}],
			Join[
				Table[field[i], {i, initialConditions[[All, 1]]}],
				Table[momentum[i], {i, initialConditions[[All, 1]]}],
				{efoldings}
			],
			{time, 0, tEnd},
			MaxSteps -> Infinity,
			DiscreteVariables -> {finalDensity, finalDensityStartTime}]];
	If[Head[solution] === NDSolve,
		$Failed, (* something is wrong with NDSolve inputs *)
		integrationTime = (efoldings /. solution)[[1, 1, 1, 2]];
		Join[
			Association[solution[[1]] /. {
				field[label_] :> label,
				momentum[label_] :> label',
				efoldings -> "Efoldings"}],
			<|
				"FinalDensitySign" -> finalDensitySign,
				"IntegrationTime" -> integrationTime,
				"TotalEfoldings" -> Switch[finalDensitySign,
					-1, Indeterminate,
					 0, (efoldings /. solution)[[1]][integrationTime],
					+1, Infinity,
					Missing[___], $StoppedEarlyMissing]|>]]
]


(* ::Subsection:: *)
(*CosmologicalHorizonExitTime*)


CosmologicalHorizonExitTime::usage = StringRiffle[{
	"CosmologicalHorizonExitTime[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] yields the time at " <>
		"which a scale specified by \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\) exits cosmological horizon during " <>
		"inflation produced by a model with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), starting with initial " <>
		"conditions \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\) for the field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\).",
	"CosmologicalHorizonExitTime[\!\(\*
StyleBox[\"evo\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] takes the output \!\(\*
StyleBox[\"evo\", \"TI\"]\) of " <>
		"InflationEvolution as its input."},
"\n"];


$NotEnoughEfoldingsMissing =
	Missing["Unknown", "Horizon exit before start of integration."];


CosmologicalHorizonExitTime[
		evolution_Association, pivotEfoldings_ ? NumericQ] := Module[
	{totalEfoldings, horizonExitEfoldings, t},
	totalEfoldings = evolution["TotalEfoldings"];
	Switch[totalEfoldings,
		\[Infinity],
			\[Infinity],
		Indeterminate,
			Indeterminate,
		x_ ? (# < pivotEfoldings &),
			$NotEnoughEfoldingsMissing,
		_,
			horizonExitEfoldings = totalEfoldings - pivotEfoldings;
			t /. FindRoot[
					evolution["Efoldings"][t] - horizonExitEfoldings,
					{t, 0, evolution["IntegrationTime"]}]
	]
]


Options[CosmologicalHorizonExitTime] = Options[InflationEvolution];


CosmologicalHorizonExitTime[
		lagrangian_,
		initialConditions_,
		time_,
		pivotEfoldings_ ? NumericQ,
		o : OptionsPattern[]] :=
	CosmologicalHorizonExitTime[
		InflationEvolution[lagrangian, initialConditions, time, o], pivotEfoldings]


(* ::Subsection:: *)
(*InflationQ*)


InflationQ::usage = StringRiffle[{
	"InflationQ[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] " <>
		"yields True if inflation stops and produces at least \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\) number of " <>
		"e-foldings.",
	"InflationQ[\!\(\*
StyleBox[\"evo\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] " <>
		"takes the output \!\(\*
StyleBox[\"evo\", \"TI\"]\) of InflationEvolution as its input."},
"\n"];


InflationQ[evolution_Association, pivotEfoldings_ ? NumericQ] := (
	evolution["FinalDensitySign"] == 0 && pivotEfoldings < evolution["TotalEfoldings"]
) === True


Options[InflationQ] = Options[InflationEvolution];


InflationQ[
		lagrangian_,
		initialConditions_,
		time_,
		pivotEfoldings_ ? NumericQ,
		o : OptionsPattern[]] :=
	InflationQ[
		InflationEvolution[lagrangian, initialConditions, time, o],
		pivotEfoldings]


(* ::Section:: *)
(*Observables*)


(* ::Subsection:: *)
(*InflationProperty*)


InflationProperty::usage =
	"InflationProperty[\!\(\*
StyleBox[\"var\", \"TI\"]\), \!\(\*
StyleBox[\"t\", \"TI\"]\)]" <>
		"represents an inflation variable \!\(\*
StyleBox[\"var\", \"TI\"]\) at time \!\(\*
StyleBox[\"t\", \"TI\"]\).";


Options[InflationProperty] = {Method -> Automatic};


InflationProperty /: MakeBoxes[
		InflationProperty[obs_String, time_, o : OptionsPattern[]],
		StandardForm] := TemplateBox[
	{
		"\<\"" <> obs <> "\"\>",
		"\<\"" <> StringRiffle[{
			If[StringQ[time], time, "t = " <> ToString[time]],
			With[{method = OptionValue[InflationProperty, o, Method]},
				If[method === Automatic, Nothing, method]
			]
		}, ", "] <> "\"\>"
	},
	"InflationValue",
	DisplayFunction -> (FrameBox[
		PanelBox[
			GridBox[
				{{
					StyleBox[
						#1,
						Bold,
						FontSize -> 13,
						FontColor -> RGBColor[0.061158, 0.20595, 0.395437]],
					StyleBox[
						RowBox[{"(", #2, ")"}],
						FontColor -> GrayLevel[0.65],
						FontSize -> 13,
						FontWeight -> "Plain"]
				}},
				GridBoxSpacings -> {"Columns" -> {{0.2}}, "Rows" -> {{0}}}, 
				BaselinePosition -> {1, 1}
			],
			Background -> RGBColor[0.921569, 0.980392, 1.],
			BaselinePosition -> Baseline,
			FrameMargins -> {{5, 5}, {1.5, 1.5}},
			BaseStyle -> {FontFamily -> "Helvetica"}
		],
		FrameMargins -> None,
		FrameStyle -> RGBColor[0., 0.504768, 1.],
		BaselinePosition -> Baseline,
		RoundingRadius -> 4
	] &),
	InterpretationFunction ->
		(RowBox[{"InflationProperty", "[", RowBox[{#1, ",", #2}], "]"}] &),
	Editable -> False,
	Selectable -> False
]


(* ::Subsection:: *)
(*InflationValue*)


(* ::Subsubsection:: *)
(*InflationValue implementation*)


InflationValue::usage = StringRiffle[{
	"InflationValue[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\), \!\(\*
StyleBox[\"property\", \"TI\"]\)] " <>
		"yield the value of a specified \!\(\*
StyleBox[\"property\", \"TI\"]\) for a specified model.",
	"InflationValue[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\), {\!\(\*SubscriptBox[
StyleBox[\"p\", \"TI\"], 
StyleBox[\"1\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"p\", \"TI\"], 
StyleBox[\"2\", \"TR\"]]\), \!\(\*
StyleBox[\"\[Ellipsis]\", \"TR\"]\)}] " <>
		"yields a list of values for properties \!\(\*SubscriptBox[
StyleBox[\"p\", \"TI\"], 
StyleBox[\"1\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"p\", \"TI\"], 
StyleBox[\"2\", \"TR\"]]\), \!\(\*
StyleBox[\"\[Ellipsis]\", \"TR\"]\)"},
"\n"];


Options[InflationValue] = Options[InflationEvolution];


InflationValue[
		lagrangian_,
		initialConditions_,
		time_,
		pivotEfoldings_ ? NumericQ,
		properties_List,
		o : OptionsPattern[]] := $InflationValueInternalData[
			lagrangian, initialConditions, time, pivotEfoldings, properties, o][
				"Values"]


InflationValue[
		lagrangian_,
		initialConditions_,
		time_,
		pivotEfoldings_ ? NumericQ,
		property_InflationProperty,
		o : OptionsPattern[]] := InflationValue[
			lagrangian, initialConditions, time, pivotEfoldings, {property}, o][[1]]


(* ::Subsubsection:: *)
(*$ExplicitProperty*)


ClearAll[$EvaluateProperty];


$EvaluateProperty[InflationProperty[prop_, time_, o : OptionsPattern[]]] :=
		$ExplicitProperty[prop, time, OptionValue[InflationProperty, o, Method]];


ClearAll[$ExplicitProperty];


$ExplicitProperty[prop_, time_, Automatic] := $ExplicitProperty[prop, time]


(* ::Subsubsection:: *)
(*$InflationValueInternalData*)


(* ::Text:: *)
(*START HERE*)


ClearAll[$InflationValueInternalData];


$InflationValueInternalData[
		lagrangian_,
		initialConditions_,
		time_,
		pivotEfoldings_ ? NumericQ,
		properties_List,
		opts : OptionsPattern[]] := Module[{
				evolution, integrationTime, totalEfoldingsCount,
				explicitProperties, propertiesByTime, valuesByTime},
	explicitProperties = $EvaluateProperty /@ properties;
	evolution = InflationEvolution[lagrangian, initialConditions, time, opts];
	integrationTime = evolution["IntegrationTime"];
	totalEfoldingsCount = evolution["TotalEfoldings"];
	propertiesByTime = KeyMap[
		# /. {
			"Start" -> 0.0,
			"HorizonExit" -> CosmologicalHorizonExitTime[evolution, pivotEfoldings],
			"End" -> integrationTime
		} &,
		Merge[
			Association[{Reverse[#]}] & /@
					Thread[explicitProperties -> explicitProperties[[All, 2]]],
			Join]];
	valuesByTime = Join @@ KeyValueMap[
		Association @ Switch[#1,
			_ ? MissingQ,
				Table[property -> #1, {property, #2}],
			\[Infinity],
				Table[
					property -> $NotEnoughEfoldingsMissing,
					{property, #2}],
			_,
				Thread[#2 -> $InflationValue[
					lagrangian,
					initialConditions[[All, 1]],
					time,
					evolution,
					#2[[All, 1]],
					#1]]
		] &,
		propertiesByTime
	];
	<|
		"Evolution" -> evolution,
		"IntegrationTime" -> integrationTime,
		"Values" -> (explicitProperties /. valuesByTime)
	|>
]


(* ::Subsubsection::Closed:: *)
(*InflationPropertyData*)


InflationPropertyData::usage = StringRiffle[{
	"InflationPropertyData[] " <>
		"gives the list of all properties supported by InflationProperty and " <>
		"InflationValue.",
	"InflationPropertyData[\!\(\*
StyleBox[\"p\", \"TI\"]\)] " <>
		"gives the list of methods supported for property \!\(\*
StyleBox[\"p\", \"TI\"]\)."
}, "\n"];


(* ::Text:: *)
(*The values are added later in the implementation.*)


InflationPropertyData[] = {};


InflationPropertyData[property_String] := {};


(* ::Subsubsection:: *)
(*$InflationValue*)


ClearAll[$InflationValue];


$InflationValue[
		lagrangian_,
		fields_,
		time_,
		evolution_Association,
		properties_List,
		lookupTime_ ? NumericQ] := Module[{
			derivedExpressions, rawPropertyNames, derivativePropertyNames,
			derivativePropertyValues, derivedPropertyNames,
			derivedPropertyValues},
	derivedExpressions = properties //. $DerivedValues;
	rawPropertyNames = Union[Cases[
		derivedExpressions,
		_String | _ ? (MemberQ[Join[fields, Thread[fields']], #] &),
		{0, \[Infinity]}]];
	(*derivativePropertyNames =
			Select[MemberQ[Keys[$EvolutionDerivativeSpecs], #] &] @ rawPropertyNames;
	derivativePropertyValues = $DerivativeValues[
			lagrangian, fields, time, evolution, derivativePropertyNames, lookupTime];*)
		(**) derivativePropertyNames = {}; derivativePropertyValues = {};
	derivedPropertyNames = Complement[rawPropertyNames, derivativePropertyNames];
	derivedPropertyValues = $InflationValue[
			lagrangian, fields, time, evolution, #, lookupTime] &
					/@ derivedPropertyNames;
	Quiet[
		derivedExpressions /. Join[
			Thread[derivativePropertyNames -> derivativePropertyValues],
			Thread[derivedPropertyNames -> derivedPropertyValues]],
		{Power::infy, Infinity::indet}]
]


(* ::Subsubsection::Closed:: *)
(*$AddToSet*)


ClearAll[$AddToSet];
$AddToSet[set_, items_List] := Union[If[ListQ[set], Join[set, items], items]];
$AddToSet[set_, item_] := $AddToSet[set, {item}]


(* ::Subsubsection:: *)
(*Time*)


(* ::Text:: *)
(*Time simply returns its argument.*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"Time"}];


$InflationValue[
		lagrangian_,
		fields_,
		time_,
		evolution_Association,
		"Time",
		lookupTime_ ? NumericQ] :=
	lookupTime


(* ::Subsubsection:: *)
(*Elementary observables*)


(* ::Text:: *)
(*First, we evaluate trivial observables, which we have already computed as part of the evolution, i.e. the value of the field, e-foldings, and their derivatives.*)


InflationPropertyData[] = $AddToSet[
		InflationPropertyData[], {"Efoldings"}];


$InflationValue[
		lagrangian_,
		fields_,
		time_,
		evolution_Association,
		property_,
		lookupTime_ ? NumericQ] /;
			MemberQ[Join[{"Efoldings"}, fields, Thread[fields']], property] :=
	evolution[property][lookupTime]


(* ::Subsubsection::Closed:: *)
(*Derivatives of elementary observables*)


(* ::Text:: *)
(*It is also useful to derive derivatives up to the fourth order of the field and the number of e-foldings.*)


(* ::Text:: *)
(*To derive these derivatives, we are going to use the Euler-Lagrange equation and Friedman equation to analytically compute them. This way, we will avoid large numerical errors, which appear if we try to numerically differentiate function like the Hubble parameter, which are nearly constant.*)


$EvolutionDerivativeSpecs = <|
	"FieldTimeDerivative" -> {"FieldTimeDerivative", 0},
	"FieldSecondTimeDerivative" -> {"FieldTimeDerivative", 1},
	"FieldThirdTimeDerivative" -> {"FieldTimeDerivative", 2},
	"FieldFourthTimeDerivative" -> {"FieldTimeDerivative", 3},
	"EfoldingsTimeDerivative" -> {"Efoldings", 1},
	"EfoldingsSecondTimeDerivative" -> {"Efoldings", 2},
	"EfoldingsThirdTimeDerivative" -> {"Efoldings", 3},
	"EfoldingsFourthTimeDerivative" -> {"Efoldings", 4}
|>;


InflationPropertyData[] =
		$AddToSet[InflationPropertyData[], Keys[$EvolutionDerivativeSpecs]];


ClearAll[$DerivativeValues];


$DerivativeValues[
		lagrangian_,
		field_,
		time_,
		evolution_Association,
		properties_List,
		lookupTime_ ? NumericQ] := Module[{
				specs, highestDerivative, fieldDerivatives,
				fieldReplacementRules, specAnswers, efoldingsDerivativeAnswer},
	specs = properties /. $EvolutionDerivativeSpecs;
	highestDerivative = Max[
			specs /. {{"FieldTimeDerivative", k_} :> k + 1, {"Efoldings", k_} :> k},
			0];
	fieldDerivatives = <||>;
	fieldReplacementRules = {
		field :> fieldDerivatives[0],
		D[field, {time, order_}] :> fieldDerivatives[order]
	};
	fieldDerivatives[0] = $InflationValue[
			lagrangian, field, time, evolution, "Field", lookupTime];
	fieldDerivatives[1] = $InflationValue[
			lagrangian, field, time, evolution, "FieldTimeDerivative", lookupTime];
	Do[
		fieldDerivatives[k] = D[
			$FieldSecondTimeDerivative[lagrangian, field, D[field, time]],
			{time, k - 2}
		] /. fieldReplacementRules,
		{k, 2, highestDerivative}
	];
	specAnswers = AssociationMap[If[#[[1]] == "FieldTimeDerivative",
		fieldDerivatives[#[[2]] + 1],
		D[
			$EfoldingsTimeDerivative[lagrangian, field, D[field, time]],
			{time, #[[2]] - 1}
		] /. fieldReplacementRules
	] &][specs];
	Values[KeyMap[# /. Reverse /@ Normal[$EvolutionDerivativeSpecs] &][specAnswers]]
]


$InflationValue[
		lagrangian_,
		field_,
		time_,
		evolution_Association,
		property_String ? (MemberQ[Keys[$EvolutionDerivativeSpecs], #] &),
		lookupTime_ ? NumericQ] :=
	$DerivativeValues[lagrangian, field, time, evolution, {property}, lookupTime][[1]]


(* ::Subsubsection::Closed:: *)
(*$InflationValue for derived values*)


(* ::Text:: *)
(*Many of the observables we are going to use, including \[Epsilon] are going to be simple algebraic functions of other observables. In order to calculate cases like that, we are going to implement a general function.*)


$InflationValue[
		lagrangian_,
		field_,
		time_,
		evolution_Association,
		property_String,
		lookupTime_ ? NumericQ] /; MemberQ[Keys[$DerivedValues], property] :=
	$InflationValue[lagrangian, field, time, evolution, {property}, lookupTime][[1]]


$DerivedValues = {};


(* ::Subsubsection::Closed:: *)
(*Hubble parameter*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {
	"HubbleParameter",
	"HubbleParameterTimeDerivative",
	"HubbleParameterSecondTimeDerivative",
	"HubbleParameterThirdTimeDerivative"
}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"HubbleParameter" -> "EfoldingsTimeDerivative",
	"HubbleParameterTimeDerivative" -> "EfoldingsSecondTimeDerivative",
	"HubbleParameterSecondTimeDerivative" -> "EfoldingsThirdTimeDerivative",
	"HubbleParameterThirdTimeDerivative" -> "EfoldingsFourthTimeDerivative"
}];


(* ::Subsubsection::Closed:: *)
(*Lagrangian, potential, density, and pressure, and their derivatives with respect to the field and time*)


(* ::Text:: *)
(*Some of the observables we are going to compute depend not only on the evolution of the fields and e-foldings, but also on the Lagrangian itself. For that reason, we will need to derive multiple observables that have to do with the value of the Lagrangian, density and pressure, and their derivatives with respect to the time derivative of the field, and with respect to time.*)


ClearAll[$PropertyExpression];


$PropertyExpression[lagrangian_, field_, time_, {"Lagrangian", 0, 0, 0}] := lagrangian


$PropertyExpression[lagrangian_, field_, time_, {"Potential", 0, 0, 0}] :=
		- lagrangian /. D[field, time] -> 0


$PropertyExpression[
		lagrangian_, field_, time_, {obs : "Density" | "Pressure", 0, 0, 0}] :=
	If[obs === "Density", InflatonDensity, InflatonPressure][lagrangian, field, time]


$PropertyExpression[
		lagrangian_,
		field_,
		time_,
		{obs : "Lagrangian" | "Potential" | "Density" | "Pressure",
		 fieldOrder_,
		 fieldVelocityOrder_,
		 timeOrder_}] :=
	Module[
			{noDerivative, fieldDerivative, fieldVelocityDerivative, timeDerivative},
		noDerivative = $PropertyExpression[lagrangian, field, time, {obs, 0, 0, 0}];
		fieldDerivative = D[noDerivative, {field, fieldOrder}];
		fieldVelocityDerivative =
				D[fieldDerivative, {D[field, time], fieldVelocityOrder}];
		timeDerivative = D[fieldVelocityDerivative, {time, timeOrder}]
	]


ClearAll[$LagrangianDerivativeSpecs];


$LagrangianDerivativeSpecs = <|
	"Lagrangian" -> {"Lagrangian", 0, 0, 0},
	"Potential" -> {"Potential", 0, 0, 0},
	"PotentialFieldDerivative" -> {"Potential", 1, 0, 0},
	"PotentialSecondFieldDerivative" -> {"Potential", 2, 0, 0},
	"LagrangianSecondFieldVelocityDerivative" -> {"Lagrangian", 0, 2, 0},
	"LagrangianThirdFieldVelocityDerivative" -> {"Lagrangian", 0, 3, 0},
	"LagrangianThirdFieldVelocityDerivativeTimeDerivative" -> {"Lagrangian", 0, 3, 1},
	"Density" -> {"Density", 0, 0, 0},
	"DensityFieldVelocityDerivative" -> {"Density", 0, 1, 0},
	"DensityFieldVelocityDerivativeTimeDerivative" -> {"Density", 0, 1, 1},
	"Pressure" -> {"Pressure", 0, 0, 0},
	"PressureFieldVelocityDerivative" -> {"Pressure", 0, 1, 0},
	"PressureFieldVelocityDerivativeTimeDerivative" -> {"Pressure", 0, 1, 1}
|>;


InflationPropertyData[] =
		$AddToSet[InflationPropertyData[], Keys[$LagrangianDerivativeSpecs]];


$InflationValue[
		lagrangian_,
		field_,
		time_,
		evolution_Association,
		property_String ? (MemberQ[Keys[$LagrangianDerivativeSpecs], #] &),
		lookupTime_ ? NumericQ] :=
	$PropertyExpression[
			lagrangian, field, time, $LagrangianDerivativeSpecs[property]] /. {
		field -> $InflationValue[
				lagrangian, field, time, evolution, "Field", lookupTime],
		D[field, time] -> $InflationValue[
				lagrangian,
				field,
				time,
				evolution,
				"FieldTimeDerivative",
				lookupTime],
		D[field, {time, 2}] -> $InflationValue[
				lagrangian,
				field,
				time,
				evolution,
				"FieldSecondTimeDerivative",
				lookupTime]
	}


(* ::Subsubsection:: *)
(*Slow-roll parameter \[Epsilon] and and its derivative*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {
	"SlowRollEpsilon", "SlowRollEpsilonTimeDerivative"
}];


InflationPropertyData["SlowRollEpsilon"] = {"FromHubbleParameter", "FromPotential"};


$ExplicitProperty["SlowRollEpsilon", time_, "FromHubbleParameter"...] :=
	$ExplicitProperty["SlowRollEpsilonFromHubbleParameter", time]


$ExplicitProperty["SlowRollEpsilon", time_, "FromPotential"] :=
	$ExplicitProperty["SlowRollEpsilonFromPotential", time]


(* ::Text:: *)
(*Using Hubble parameter*)


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollEpsilonFromHubbleParameter" ->
			- "HubbleParameterTimeDerivative" / ("HubbleParameter")^2,
	"SlowRollEpsilonTimeDerivative" ->
			(2 ("HubbleParameterTimeDerivative")^2
					- "HubbleParameter" "HubbleParameterSecondTimeDerivative")
			/ ("HubbleParameter")^3
}];


(* ::Text:: *)
(*Using potential*)


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollEpsilonFromPotential" ->
			1/2 ("PotentialFieldDerivative" / "Potential")^2
}];


(* ::Subsubsection:: *)
(*Slow-roll parameter \[Eta]*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"SlowRollDynamicEta"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollDynamicEta" ->
			"SlowRollEpsilonTimeDerivative" /
				("SlowRollEpsilonFromHubbleParameter" "HubbleParameter")
}];


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"SlowRollPotentialEta"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollPotentialEta" -> "PotentialSecondFieldDerivative" / "Potential"
}];


(* ::Subsubsection::Closed:: *)
(*Effective axion decay constant*)


InflationPropertyData[] =
		$AddToSet[InflationPropertyData[], {"EffectiveAxionDecayConstant"}];


InflationPropertyData["EffectiveAxionDecayConstant"] =
		{"FromHubbleParameter", "FromPotential"};


$ExplicitProperty["EffectiveAxionDecayConstant", time_, "FromHubbleParameter"...] :=
	$ExplicitProperty["EffectiveAxionDecayConstantFromHubbleParameter", time]


$ExplicitProperty["EffectiveAxionDecayConstant", time_, "FromPotential"] :=
	$ExplicitProperty["EffectiveAxionDecayConstantFromPotential", time]


(* ::Text:: *)
(*From Hubble parameter*)


$DerivedValues = $AddToSet[$DerivedValues, {
	"EffectiveAxionDecayConstantFromHubbleParameter" ->
			1 / Sqrt["SlowRollDynamicEta" - 2 "SlowRollEpsilonFromHubbleParameter"]
}];


(* ::Text:: *)
(*From potential*)


$DerivedValues = $AddToSet[$DerivedValues, {
	"EffectiveAxionDecayConstantFromPotential" ->
			1 / Sqrt[2 ("SlowRollEpsilonFromPotential" - "SlowRollPotentialEta")]
}];


(* ::Subsubsection::Closed:: *)
(*Speed of sound and its derivative*)


InflationPropertyData[] = $AddToSet[
		InflationPropertyData[], {"SpeedOfSound", "SpeedOfSoundTimeDerivative"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"SpeedOfSound" ->
			Sqrt["PressureFieldVelocityDerivative" / "DensityFieldVelocityDerivative"],
	"SpeedOfSoundTimeDerivative" ->
			("DensityFieldVelocityDerivative"
						* "PressureFieldVelocityDerivativeTimeDerivative"
					- "PressureFieldVelocityDerivative"
						* "DensityFieldVelocityDerivativeTimeDerivative")
				/ (2 Sqrt[
					"PressureFieldVelocityDerivative"
						* "DensityFieldVelocityDerivative"])
}];


(* ::Subsubsection::Closed:: *)
(*Slow roll parameter s*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"SlowRollS"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollS" -> "SpeedOfSoundTimeDerivative" / ("SpeedOfSound" "HubbleParameter")
}];


(* ::Subsubsection::Closed:: *)
(*Scalar and tensor spectral indices*)


InflationPropertyData[] = $AddToSet[
		InflationPropertyData[], {"ScalarSpectralIndex", "TensorSpectralIndex"}];


InflationPropertyData["ScalarSpectralIndex"] =
		{"FromHubbleParameter", "FromPotential"};


$ExplicitProperty["ScalarSpectralIndex", time_, "FromHubbleParameter"...] :=
	$ExplicitProperty["ScalarSpectralIndexFromHubbleParameter", time]


$ExplicitProperty["ScalarSpectralIndex", time_, "FromPotential"] :=
	$ExplicitProperty["ScalarSpectralIndexFromPotential", time]


InflationPropertyData["TensorSpectralIndex"] =
		{"FromHubbleParameter", "FromPotential"};


$ExplicitProperty["TensorSpectralIndex", time_, "FromHubbleParameter"...] :=
	$ExplicitProperty["TensorSpectralIndexFromHubbleParameter", time]


$ExplicitProperty["TensorSpectralIndex", time_, "FromPotential"] :=
	$ExplicitProperty["TensorSpectralIndexFromPotential", time]


(* ::Text:: *)
(*From Hubble parameter*)


$DerivedValues = $AddToSet[$DerivedValues, {
	"ScalarSpectralIndexFromHubbleParameter" -> 1
			- 2 "SlowRollEpsilonFromHubbleParameter"
			- "SlowRollDynamicEta"
			- "SlowRollS",
	"TensorSpectralIndexFromHubbleParameter" ->
			- 2 "SlowRollEpsilonFromHubbleParameter"
}];


(* ::Text:: *)
(*From potential*)


$DerivedValues = $AddToSet[$DerivedValues, {
	"ScalarSpectralIndexFromPotential" -> 1
			- 6 "SlowRollEpsilonFromPotential"
			+ 2 "SlowRollPotentialEta",
	"TensorSpectralIndexFromPotential" ->
			- 2 "SlowRollEpsilonFromPotential"
}];


(* ::Subsubsection::Closed:: *)
(*Scalar and tensor power spectra*)


InflationPropertyData[] = $AddToSet[
		InflationPropertyData[], {"ScalarPowerSpectrum", "TensorPowerSpectrum"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"ScalarPowerSpectrum" ->
			1/(8 \[Pi]^2) "HubbleParameter"^2 /
					("SpeedOfSound" "SlowRollEpsilonFromHubbleParameter"),
	"TensorPowerSpectrum" -> 2/(3 \[Pi]^2) "Density"
}];


(* ::Subsubsection:: *)
(*Tensor-to-scalar ratio*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"TensorToScalarRatio"}];


InflationPropertyData["TensorToScalarRatio"] =
		{"FromHubbleParameter", "FromPotential"};


$ExplicitProperty["TensorToScalarRatio", time_, "FromHubbleParameter"...] :=
	$ExplicitProperty["TensorToScalarRatioFromHubbleParameter", time]


$ExplicitProperty["TensorToScalarRatio", time_, "FromPotential"] :=
	$ExplicitProperty["TensorToScalarRatioFromPotential", time]


$DerivedValues = $AddToSet[$DerivedValues, {
	"TensorToScalarRatioFromHubbleParameter" ->
			"TensorPowerSpectrum" / "ScalarPowerSpectrum",
	"TensorToScalarRatioFromPotential" -> 16 "SlowRollEpsilonFromPotential"
}];


(* ::Subsubsection::Closed:: *)
(*Non-Gaussianity amplitude*)


InflationPropertyData[] = $AddToSet[
		InflationPropertyData[], {"z1", "z2", "z", "NonGaussianityAmplitude"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"z1" -> 1/2 ("FieldTimeDerivative")^2 "LagrangianSecondFieldVelocityDerivative",
	"z2" -> 1/12 ("FieldTimeDerivative")^3 "LagrangianThirdFieldVelocityDerivative",
	"z" -> 1/("HubbleParameter") (
		"LagrangianThirdFieldVelocityDerivativeTimeDerivative"
				/ "LagrangianThirdFieldVelocityDerivative"
			+ 3 ("FieldSecondTimeDerivative")/("FieldTimeDerivative")),
	"NonGaussianityAmplitude" -> 35 / 108 (1 / "SpeedOfSound"^2 - 1)
			- 5 / 81 ((1 / "SpeedOfSound"^2 - 1 - 2 "z2" / "z1")
				+ (3 - 2 EulerGamma) "z" "z2" / "z1")
}];


(* ::Section:: *)
(*Comparison with Experiment*)


(* ::Subsection:: *)
(*ExperimentallyConsistentInflationQ*)


ExperimentallyConsistentInflationQ::usage = StringRiffle[{
	"ExperimentallyConsistentInflationQ[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] " <>
		"yields True if the specified model results in inflation with " <>
		"experimentally consistent observables, and False otherwise.",
	"ExperimentallyConsistentInflationQ[\!\(\*SubscriptBox[
StyleBox[\"n\", \"TI\"], 
StyleBox[\"s\", \"TI\"]]\), \!\(\*
StyleBox[\"r\", \"TI\"]\)] " <>
		"yields True if a given index of scalar spectral perturbations " <>
		"\!\(\*SubscriptBox[
StyleBox[\"n\", \"TI\"], 
StyleBox[\"s\", \"TI\"]]\) and " <>
		"tensor-to-scalar power spectrum ratio \!\(\*
StyleBox[\"r\", \"TI\"]\) are consistent with experimental " <>
		"bounds, and False otherwise."
}, "\n"];


Options[ExperimentallyConsistentInflationQ] = Options[InflationEvolution];


ClearAll[$PlanckScalarIndexTensorToScalarRatioRegion];
$PlanckScalarIndexTensorToScalarRatioRegion = Region @ Polygon @ Rest @ Import @
		PacletManager`PacletResource[
				"InflationSimulator", "PlanckConstraints-TT_TE_EE_lowP-95CL.csv"];


ExperimentallyConsistentInflationQ[ns_ ? NumericQ, r_ ? NumericQ] :=
	RegionMember[$PlanckScalarIndexTensorToScalarRatioRegion, {ns, r}]


ExperimentallyConsistentInflationQ[
			lagrangian_,
			{field_, fieldInitial_ ? NumericQ, fieldDerivativeInitial_ ? NumericQ},
			time_,
			pivotEfoldings_ ? NumericQ,
			o : OptionsPattern[]] := With[
		{evolution = InflationEvolution[
				lagrangian, {field, fieldInitial, fieldDerivativeInitial}, time, o]},
	InflationQ[evolution, pivotEfoldings] &&
			ExperimentallyConsistentInflationQ @@ $InflationValue[
					lagrangian,
					field,
					time,
					evolution,
					{"ScalarSpectralIndexFromHubbleParameter",
					 "TensorToScalarRatioFromHubbleParameter"},
					CosmologicalHorizonExitTime[evolution, pivotEfoldings]]
]


(* ::Chapter::Closed:: *)
(*End*)


Protect @@@ InflationSimulator`Private`$PublicSymbols;


End[];


EndPackage[];
