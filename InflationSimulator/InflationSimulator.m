(* ::Package:: *)

(* ::Title:: *)
(*Inflation Simulator*)


(* ::Chapter:: *)
(*Begin*)


(* ::Text:: *)
(*See on GitHub: https://github.com/maxitg/InflationSimulator.*)


BeginPackage["InflationSimulator`", {"UsageString`"}];


ClearAll[$InflationProperties];


InflationSimulator`Private`$PublicSymbols = {
	InflatonDensity, InflatonPressure, InflationEquationsOfMotion,
	InflationEvolution, InflationStopsQ, InflationEfoldingsCount,
		CosmologicalHorizonExitTime, InflationQ,
	InflationProperty, $InflationProperties, InflationValue};


Unprotect @@ InflationSimulator`Private`$PublicSymbols;
ClearAll @@ InflationSimulator`Private`$PublicSymbols;


(* ::Chapter:: *)
(*Implementation*)


Begin["`Private`"];


(* ::Section:: *)
(*Equations of Motion*)


(* ::Subsection::Closed:: *)
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
$InflatonDensity[lagrangian_, fieldDot_] :=
	-lagrangian + D[lagrangian, fieldDot] fieldDot


InflatonDensity[lagrangian_, field_, time_] :=
	$InflatonDensity[lagrangian, D[field, time]]


(* ::Subsection::Closed:: *)
(*InflatonPressure*)


InflatonPressure::usage = "InflatonPressure[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields the pressure of a homogeneous field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)] with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\).";


InflatonPressure[lagrangian_, field_, time_] := lagrangian


(* ::Subsection::Closed:: *)
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
$FieldSecondTimeDerivative[lagrangian_, field_, fieldDot_] :=
	(- Sqrt[3 (-lagrangian + D[lagrangian, fieldDot] fieldDot)]
			* D[lagrangian, fieldDot]
		+ D[lagrangian, field]
		- D[lagrangian, fieldDot] D[lagrangian, field, fieldDot]) /
	D[lagrangian, {fieldDot, 2}]


ClearAll[$EfoldingsTimeDerivative];
$EfoldingsTimeDerivative[lagrangian_, field_, fieldDot_] :=
	Sqrt[1/3 $InflatonDensity[lagrangian, fieldDot]]


InflationEquationsOfMotion[lagrangian_, field_, efoldings_, time_] := {
	D[field, {time, 2}] ==
			$FieldSecondTimeDerivative[lagrangian, field, D[field, time]],
	D[efoldings, time] == $EfoldingsTimeDerivative[lagrangian, field, D[field, time]]}


(* ::Section:: *)
(*Evolution*)


(* ::Subsection::Closed:: *)
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
	"Lagrangian did not evaluate to a numerical value " <>
	"for field `1` and its derivative `2`.";


InflationEvolution::inwp =
	"Insufficient working precision. Doubling working precision to `1`.";
(*Off[InflationEvolution::inwp];*)


InflationEvolution::comp =
	"Right-hand side of either Euler-Lagrange or Friedmann equation evaluated " <>
	"to a complex number.";


(* ::Subsubsection:: *)
(*Options*)


Options[InflationEvolution] = {
	"EfoldingsDerivativeThreshold" -> 16^^0.1,
	"EfoldingsThreshold" -> 16^^1000,
	"FieldDerivativeThreshold" -> 16^^0.01,
	"FieldBounceThreshold" -> 16^^20,
	"MaxIntegrationTime" -> \[Infinity],
	WorkingPrecision -> Automatic,
	PrecisionGoal -> MachinePrecision / 2,
	"Debug" -> False
};


(* ::Subsubsection:: *)
(*Implementation*)


ClearAll[$IntegrationTime];
$IntegrationTime[solution_] := solution["Efoldings"][[1, 1, 2]];


ClearAll[$SetPrecision];
$SetDoublePrecision[expr_, precision_ ? NumericQ] := SetPrecision[expr, 2 precision]
$SetDoublePrecision[expr_, Automatic] := expr


InflationEvolution[
		inputLagrangian_,
		{field_, inputFieldInitial_ ? NumericQ,
				inputFieldDerivativeInitial_ ? NumericQ},
		time_,
		o : OptionsPattern[]] := Module[{
			workingPrecision, lagrangian, fieldInitial, fieldDerivativeInitial,
				lagrangianNumericQ,
			fieldValues, fieldDerivativeValues, efoldingsValues, bounceValue,
				debugPrint,
			evolution, t, f, ft, n, fieldBounceCount, inflationStoppedQ},
	workingPrecision = If[OptionValue[WorkingPrecision] === Automatic,
		MachinePrecision,
		OptionValue[WorkingPrecision]];
	{lagrangian, fieldInitial, fieldDerivativeInitial} = $SetDoublePrecision[
			{inputLagrangian, inputFieldInitial, inputFieldDerivativeInitial},
			OptionValue[WorkingPrecision]] /. {
				D[field, time] -> ft[t],
				field -> f[t]};
	lagrangianNumericQ = Quiet[NumericQ[lagrangian /. {
			ft[t] -> fieldDerivativeInitial, f[t] -> fieldInitial}]];
	If[!lagrangianNumericQ,
		Message[InflationEvolution::nnuml, fieldInitial, fieldDerivativeInitial]];
	If[OptionValue["Debug"],
		fieldValues = {};
		fieldDerivativeValues = {};
		efoldingsValues = {};
		bounceValue = 0;
		debugPrint = PrintTemporary[Dynamic[Refresh[Column[{
			StringTemplate[
				"Bounced `1` times. WorkingPrecision = `2` MachinePrecision."][
					Round @ bounceValue, workingPrecision/MachinePrecision],
			Quiet @ GraphicsRow[(
				ListPlot[
					#[[1]],
					PlotLabel -> #[[2]],
					Frame -> True,
					FrameLabel -> {"Time", #[[2]]}] & /@ {
						{fieldValues, "Field"},
						{fieldDerivativeValues, "FieldTimeDerivative"},
						{efoldingsValues, "Efoldings"}}),
				ImageSize -> Scaled[1]]
		}], UpdateInterval -> 1]]];
	];
	
	With[{messagesToCatch = {
			Power::infy, Infinity::indet, Divide::indet, NDSolve::nlnum,
			NDSolve::nrnum1, NDSolve::ndcf, NDSolve::evcvmit, NDSolve::ndnum,
			Greater::nord, General::munfl, NDSolve::ndsz, NDSolve::nderr,
			InflationEvolution::comp}},
		Quiet[Check[
			evolution = Join[Association[(NDSolve[
				{
					f[0] == fieldInitial,
					ft[0] == fieldDerivativeInitial,
					f'[t] == ft[t],
					{ft'[t], n'[t]} == {
						$FieldSecondTimeDerivative[lagrangian, f[t], ft[t]],
						$EfoldingsTimeDerivative[lagrangian, f[t], ft[t]]
					},
					n[0] == 0,
					fieldBounceCount[0] == 0,

					(* encountered complex field *)
					WhenEvent[Im[f[t]] != 0,
						Message[InflationEvolution::comp];
						"StopIntegration"
					],

					(* efoldings stopped increasing *)
					WhenEvent[t n'[t] <
								n[t] OptionValue["EfoldingsDerivativeThreshold"],
						inflationStoppedQ = True;
						"StopIntegration",
						"LocationMethod" -> "StepEnd"
					],

					(* field stopped after max e-foldings reached *)
					WhenEvent[t Abs[ft[t]] <
							Abs[f[t] - fieldInitial]
								OptionValue["FieldDerivativeThreshold"],
						If[n[t] > OptionValue["EfoldingsThreshold"], 
							inflationStoppedQ = False;
							"StopIntegration"
						],
						"LocationMethod" -> "StepEnd"
					],

					(* max e-foldings reached after field stopped *)
					WhenEvent[n[t] > OptionValue["EfoldingsThreshold"],
						If[t Abs[ft[t]] <
								Abs[f[t] - fieldInitial]
									OptionValue["FieldDerivativeThreshold"], 
							inflationStoppedQ = False;
							"StopIntegration"
						],
						"LocationMethod" -> "StepEnd"
					],

					(* field bounced *)
					WhenEvent[f'[t] == 0,
						If[fieldBounceCount[t] ==
								OptionValue["FieldBounceThreshold"] - 1,
							inflationStoppedQ = False; "StopIntegration",
							fieldBounceCount[t] -> fieldBounceCount[t] + 1
						],
						"LocationMethod" -> "StepEnd"
					]
				},
				{f, ft, n, fieldBounceCount},
				{t, 0, OptionValue["MaxIntegrationTime"]},
				MaxSteps -> Infinity,
				DiscreteVariables -> fieldBounceCount,
				WorkingPrecision -> workingPrecision,
				PrecisionGoal -> OptionValue[PrecisionGoal],
				If[OptionValue["Debug"],
					EvaluationMonitor :> (
						AppendTo[fieldValues, {t, f[t]}];
						AppendTo[fieldDerivativeValues, {t, ft[t]}];
						AppendTo[efoldingsValues, {t, n[t]}];
						If[Length[fieldValues] > 1000,
							fieldValues = Rest[fieldValues]];
						If[Length[fieldDerivativeValues] > 1000,
							fieldDerivativeValues = Rest[fieldDerivativeValues]
						];
						If[Length[efoldingsValues] > 1000,
							efoldingsValues = Rest[efoldingsValues]
						];
						bounceValue = fieldBounceCount[t];
					),
					{}
				]
			] /. {
				HoldPattern[NDSolve[_, _, ___]] :> {
					f -> $Failed,
					ft -> $Failed,
					n -> $Failed,
					fieldBounceCount -> $Failed
				}
			})[[1]] /. {
				f -> "Field",
				ft -> "FieldTimeDerivative",
				n -> "Efoldings",
				fieldBounceCount -> "FieldBounceCount"
			}], <|"InflationStoppedQ" -> inflationStoppedQ|>];
			NotebookDelete[debugPrint];
			If[Head[evolution["Field"][$IntegrationTime[evolution]]] === Complex,
				Message[InflationEvolution::comp],
				evolution
			],
			Message[InflationEvolution::inwp, 2 workingPrecision];
			inflationStoppedQ = False;	
			InflationEvolution[
					inputLagrangian,
					{field, inputFieldInitial, inputFieldDerivativeInitial},
					time,
					WorkingPrecision -> 2 workingPrecision, o],
			{
			Power::infy, Infinity::indet, Divide::indet, NDSolve::nlnum,
			NDSolve::nrnum1, NDSolve::ndcf, NDSolve::evcvmit, NDSolve::ndnum,
			Greater::nord, General::munfl, NDSolve::ndsz, NDSolve::nderr,
			InflationEvolution::comp}
		],
		{
			Power::infy, Infinity::indet, Divide::indet, NDSolve::nlnum,
			NDSolve::nrnum1, NDSolve::ndcf, NDSolve::evcvmit, NDSolve::ndnum,
			Greater::nord, General::munfl, NDSolve::ndsz, NDSolve::nderr,
			InflationEvolution::comp}] /; lagrangianNumericQ
	]
]


(* ::Subsection::Closed:: *)
(*InflationStopsQ*)


InflationStopsQ::usage = StringRiffle[{
	"InflationStopsQ[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields True if inflation produced by a " <>
		"model with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), starting with initial conditions \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\) for the " <>
		"field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\) stops eventually, and yields False otherwise.",
	"InflationStopsQ[\!\(\*
StyleBox[\"evo\", \"TI\"]\)] takes the output \!\(\*
StyleBox[\"evo\", \"TI\"]\) of InflationEvolution as its input."},
"\n"];


InflationStopsQ[evolution_Association] := evolution["InflationStoppedQ"]


Options[InflationStopsQ] = Options[InflationEvolution];


InflationStopsQ[
		inputLagrangian_,
		{field_, inputFieldInitial_ ? NumericQ,
				inputFieldDerivativeInitial_ ? NumericQ},
		time_,
		o : OptionsPattern[]] :=
	InflationStopsQ[InflationEvolution[
			inputLagrangian,
			{field, inputFieldInitial, inputFieldDerivativeInitial},
			time,
			o]]


(* ::Subsection::Closed:: *)
(*InflationEfoldingsCount*)


InflationEfoldingsCount::usage = StringRiffle[{
	"InflationEfoldingsCount[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields the number of e-foldings " <>
		"produced by a model with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), starting with initial conditions " <>
		"\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\) for the field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)\!\(\*
StyleBox[\".\", \"TI\"]\)",
	"InflationEfoldingsCount[\!\(\*
StyleBox[\"evo\", \"TI\"]\)] takes the output \!\(\*
StyleBox[\"evo\", \"TI\"]\) of InflationEvolution as its " <>
		"input."},
"\n"];


InflationEfoldingsCount[evolution_Association] := If[!InflationStopsQ[evolution],
	\[Infinity],
	evolution["Efoldings"][$IntegrationTime[evolution]]
]


Options[InflationEfoldingsCount] = Options[InflationEvolution];


InflationEfoldingsCount[
		inputLagrangian_,
		{field_, inputFieldInitial_ ? NumericQ,
				inputFieldDerivativeInitial_ ? NumericQ},
		time_,
		o : OptionsPattern[]] :=
	InflationEfoldingsCount[InflationEvolution[
			inputLagrangian,
			{field, inputFieldInitial, inputFieldDerivativeInitial},
			time,
			o]]


(* ::Subsection::Closed:: *)
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


CosmologicalHorizonExitTime[
		evolution_Association, pivotEfoldings_ ? NumericQ] := Module[
	{totalEfoldings, horizonExitEfoldings, t},
	totalEfoldings = InflationEfoldingsCount[evolution];
	Switch[totalEfoldings,
		\[Infinity],
			\[Infinity],
		x_ ? (# < pivotEfoldings &),
				Missing["Unknown", "Horizon exit before start of integration."],
		_,
			horizonExitEfoldings = totalEfoldings - pivotEfoldings;
			t /. FindRoot[
					evolution["Efoldings"][t] - horizonExitEfoldings,
					{t, 0, $IntegrationTime[evolution]}]
	]
]


Options[CosmologicalHorizonExitTime] = Options[InflationEvolution];


CosmologicalHorizonExitTime[
		inputLagrangian_,
		{field_, inputFieldInitial_ ? NumericQ,
				inputFieldDerivativeInitial_ ? NumericQ},
		time_,
		pivotEfoldings_ ? NumericQ,
		o : OptionsPattern[]] :=
	CosmologicalHorizonExitTime[
		InflationEvolution[
			inputLagrangian,
			{field, inputFieldInitial, inputFieldDerivativeInitial},
			time,
			o],
		pivotEfoldings]


(* ::Subsection::Closed:: *)
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
	InflationStopsQ[evolution] && pivotEfoldings < InflationEfoldingsCount[evolution]
) === True


Options[InflationQ] = Options[InflationEvolution];


InflationQ[
		inputLagrangian_,
		{field_, inputFieldInitial_ ? NumericQ,
				inputFieldDerivativeInitial_ ? NumericQ},
		time_,
		pivotEfoldings_ ? NumericQ,
		o : OptionsPattern[]] :=
	InflationQ[
		InflationEvolution[
			inputLagrangian,
			{field, inputFieldInitial, inputFieldDerivativeInitial},
			time,
			o],
		pivotEfoldings]


(* ::Section:: *)
(*Observables*)


(* ::Subsection::Closed:: *)
(*InflationProperty*)


InflationProperty::usage =
	"InflationProperty[\!\(\*
StyleBox[\"var\", \"TI\"]\), \!\(\*
StyleBox[\"t\", \"TI\"]\)]" <>
		"represents an inflation variable \!\(\*
StyleBox[\"var\", \"TI\"]\) at time \!\(\*
StyleBox[\"t\", \"TI\"]\).";


InflationProperty /: MakeBoxes[
		InflationProperty[obs_String, time_], StandardForm] := TemplateBox[
	{
		"\<\"" <> obs <> "\"\>",
		"\<\"" <> If[StringQ[time], time, "t = " <> ToString[time]] <> "\"\>"
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


(* ::Subsection::Closed:: *)
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
		{field_, fieldInitial_ ? NumericQ, fieldDerivativeInitial_ ? NumericQ},
		time_,
		pivotEfoldings_ ? NumericQ,
		properties_List,
		o : OptionsPattern[]] := $InflationValueInternalData[
			lagrangian,
			{field, fieldInitial, fieldDerivativeInitial},
			time,
			pivotEfoldings,
			properties,
			o]["Values"]


InflationValue[
		lagrangian_,
		{field_, fieldInitial_ ? NumericQ, fieldDerivativeInitial_ ? NumericQ},
		time_,
		pivotEfoldings_ ? NumericQ,
		property_InflationProperty,
		o : OptionsPattern[]] := InflationValue[
			lagrangian,
			{field, fieldInitial, fieldDerivativeInitial},
			time,
			pivotEfoldings,
			{property},
			o][[1]]


(* ::Subsubsection:: *)
(*$InflationValueInternalData*)


ClearAll[$InflationValueInternalData];


$InflationValueInternalData[
		lagrangian_,
		{field_, fieldInitial_ ? NumericQ, fieldDerivativeInitial_ ? NumericQ},
		time_,
		pivotEfoldings_ ? NumericQ,
		properties_List,
		opts : OptionsPattern[]] := Module[{
				evolution, integrationTime, totalEfoldingsCount,
				propertiesByTime, valuesByTime},
	evolution = InflationEvolution[
			lagrangian, {field, fieldInitial, fieldDerivativeInitial}, time, opts];
	integrationTime = $IntegrationTime[evolution];
	totalEfoldingsCount = InflationEfoldingsCount[evolution];
	propertiesByTime = KeyMap[
		# /. {
			"Start" -> 0.0,
			"HorizonExit" -> CosmologicalHorizonExitTime[evolution, pivotEfoldings],
			"End" -> integrationTime
		} &,
		Merge[
			Association[{Reverse[#]}] & /@ Thread[properties -> properties[[All, 2]]],
			Join]];
	valuesByTime = Join @@ KeyValueMap[
		Association @ Switch[#1,
			_ ? MissingQ,
				Table[property -> #1, {property, #2}],
			\[Infinity],
				Table[
					property ->
         				Missing["Unknown", "Horizon exit after end of integration."],
					{property, #2}],
			_,
				Thread[#2 -> $InflationValue[
					lagrangian, field, time, evolution, #2[[All, 1]], #1]]
		] &,
		propertiesByTime
	];
	<|
		"Evolution" -> evolution,
		"IntegrationTime" -> integrationTime,
		"Values" -> (properties /. valuesByTime)
	|>
]


(* ::Subsubsection:: *)
(*$InflationValue*)


ClearAll[$InflationValue];


$InflationValue[
		lagrangian_,
		field_,
		time_,
		evolution_Association,
		properties_List,
		lookupTime_ ? NumericQ] := Module[{
			derivedExpressions, rawPropertyNames, derivativePropertyNames,
			derivativePropertyValues, derivedPropertyNames,
			derivedPropertyValues},
	derivedExpressions = properties //. $DerivedValues;
	rawPropertyNames = Union[Cases[derivedExpressions, _String, {0, \[Infinity]}]];
	derivativePropertyNames =
			Select[MemberQ[Keys[$EvolutionDerivativeSpecs], #] &] @ rawPropertyNames;
	derivativePropertyValues = $DerivativeValues[
			lagrangian, field, time, evolution, derivativePropertyNames, lookupTime];
	derivedPropertyNames = Complement[rawPropertyNames, derivativePropertyNames];
	derivedPropertyValues = $InflationValue[
			lagrangian, field, time, evolution, #, lookupTime] &
					/@ derivedPropertyNames;
	Quiet[
		derivedExpressions /. Join[
			Thread[derivativePropertyNames -> derivativePropertyValues],
			Thread[derivedPropertyNames -> derivedPropertyValues]],
		{Power::infy, Infinity::indet}]
]


(* ::Subsubsection:: *)
(*$AddToSet*)


ClearAll[$AddToSet];
$AddToSet[set_, items_List] := Union[If[ListQ[set], Join[set, items], items]];
$AddToSet[set_, item_] := $AddToSet[set, {item}]


(* ::Subsubsection:: *)
(*$InflationProperties*)


$InflationProperties::usage =
	"$InflationProperties " <>
		"gives the list of all properties supported by InflationProperty and " <>
		"InflationValue.";


(* ::Text:: *)
(*The values are added later in the implementation.*)


$InflationProperties = {};


(* ::Subsubsection:: *)
(*Time*)


(* ::Text:: *)
(*Time simply returns its argument.*)


$InflationProperties = $AddToSet[$InflationProperties, {"Time"}];


$InflationValue[
		lagrangian_,
		field_,
		time_,
		evolution_Association,
		"Time",
		lookupTime_ ? NumericQ] :=
	lookupTime


(* ::Subsubsection:: *)
(*Elementary observables*)


(* ::Text:: *)
(*First, we evaluate trivial observables, which we have already computed as part of the evolution, i.e. the value of the field, e-foldings, and their derivatives.*)


$InflationProperties =
		$AddToSet[$InflationProperties, {"Field", "FieldTimeDerivative", "Efoldings"}];


$InflationValue[
		lagrangian_,
		field_,
		time_,
		evolution_Association,
		property : "Field" | "FieldTimeDerivative" | "Efoldings",
		lookupTime_ ? NumericQ] :=
	evolution[property][lookupTime]


(* ::Subsubsection:: *)
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


$InflationProperties =
		$AddToSet[$InflationProperties, Keys[$EvolutionDerivativeSpecs]];


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


(* ::Subsubsection:: *)
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


(* ::Subsubsection:: *)
(*Hubble parameter*)


$InflationProperties = $AddToSet[$InflationProperties, {
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


(* ::Subsubsection:: *)
(*Slow-roll parameters \[Epsilon] and \!\(\*OverscriptBox[\(\[Epsilon]\), \(.\)]\)*)


$InflationProperties = $AddToSet[$InflationProperties, {
	"SlowRollEpsilon", "SlowRollEpsilonTimeDerivative"
}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollEpsilon" -> - "HubbleParameterTimeDerivative" / ("HubbleParameter")^2,
	"SlowRollEpsilonTimeDerivative" ->
			(2 ("HubbleParameterTimeDerivative")^2
					- "HubbleParameter" "HubbleParameterSecondTimeDerivative")
			/ ("HubbleParameter")^3
}];


(* ::Subsubsection:: *)
(*Slow-roll parameters \[Eta]*)


$InflationProperties = $AddToSet[$InflationProperties, {"SlowRollEta"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollEta" ->
			"SlowRollEpsilonTimeDerivative" / ("SlowRollEpsilon" "HubbleParameter")
}];


(* ::Subsubsection:: *)
(*Lagrangian, density, and pressure, and their derivatives with respect to the field and time*)


(* ::Text:: *)
(*Some of the observables we are going to compute depend not only on the evolution of the fields and e-foldings, but also on the Lagrangian itself. For that reason, we will need to derive multiple observables that have to do with the value of the Lagrangian, density and pressure, and their derivatives with respect to the time derivative of the field, and with respect to time.*)


ClearAll[$PropertyExpression];


$PropertyExpression[lagrangian_, field_, time_, {"Lagrangian", 0, 0}] := lagrangian


$PropertyExpression[
		lagrangian_, field_, time_, {obs : "Density" | "Pressure", 0, 0}] :=
	If[obs === "Density", InflatonDensity, InflatonPressure][lagrangian, field, time]


$PropertyExpression[
		lagrangian_,
		field_,
		time_,
		{obs : "Lagrangian" | "Density" | "Pressure",
		 fieldVelocityOrder_,
		 timeOrder_}] :=
	Module[
			{noDerivative, fieldVelocityDerivative, timeDerivative},
		noDerivative = $PropertyExpression[lagrangian, field, time, {obs, 0, 0}];
		fieldVelocityDerivative =
				D[noDerivative, {D[field, time], fieldVelocityOrder}];
		timeDerivative = D[fieldVelocityDerivative, {time, timeOrder}]
	]


ClearAll[$LagrangianDerivativeSpecs];


$LagrangianDerivativeSpecs = <|
	"Lagrangian" -> {"Lagrangian", 0, 0},
	"LagrangianSecondFieldVelocityDerivative" -> {"Lagrangian", 2, 0},
	"LagrangianThirdFieldVelocityDerivative" -> {"Lagrangian", 3, 0},
	"LagrangianThirdFieldVelocityDerivativeTimeDerivative" -> {"Lagrangian", 3, 1},
	"Density" -> {"Density", 0, 0},
	"DensityFieldVelocityDerivative" -> {"Density", 1, 0},
	"DensityFieldVelocityDerivativeTimeDerivative" -> {"Density", 1, 1},
	"Pressure" -> {"Pressure", 0, 0},
	"PressureFieldVelocityDerivative" -> {"Pressure", 1, 0},
	"PressureFieldVelocityDerivativeTimeDerivative" -> {"Pressure", 1, 1}
|>;


$InflationProperties =
		$AddToSet[$InflationProperties, Keys[$LagrangianDerivativeSpecs]];


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
(*Speed of sound Subscript[c, s] and \!\(\*OverscriptBox[*)
(*SubscriptBox[\(c\), \(s\)], \(.\)]\)*)


$InflationProperties = $AddToSet[
		$InflationProperties, {"SpeedOfSound", "SpeedOfSoundTimeDerivative"}];


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


(* ::Subsubsection:: *)
(*Slow roll parameter s*)


$InflationProperties = $AddToSet[$InflationProperties, {"SlowRollS"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollS" -> "SpeedOfSoundTimeDerivative" / ("SpeedOfSound" "HubbleParameter")
}];


(* ::Subsubsection:: *)
(*Scalar and tensor spectral indices Subscript[n, s] and Subscript[n, t]*)


$InflationProperties = $AddToSet[
		$InflationProperties, {"ScalarSpectralIndex", "TensorSpectralIndex"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"ScalarSpectralIndex" -> 1 - 2 "SlowRollEpsilon" - "SlowRollEta" - "SlowRollS",
	"TensorSpectralIndex" -> - 2 "SlowRollEpsilon"
}];


(* ::Subsubsection:: *)
(*Scalar and tensor power spectra P^\[Zeta] and P^h*)


$InflationProperties = $AddToSet[
		$InflationProperties,
		{"ScalarPowerSpectrum", "TensorPowerSpectrum", "TensorToScalarRatio"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"ScalarPowerSpectrum" -> 1/(8 \[Pi]^2) ("HubbleParameter")^2/("SpeedOfSound" "SlowRollEpsilon"),
	"TensorPowerSpectrum" -> 2/(3 \[Pi]^2) "Density",
	"TensorToScalarRatio" -> -8 "SpeedOfSound" "TensorSpectralIndex"
}];


(* ::Subsubsection:: *)
(*Non-Gaussianity amplitude Subscript[f, NL]*)


$InflationProperties =
		$AddToSet[$InflationProperties, {"z1", "z2", "z", "NonGaussianityAmplitude"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"z1" -> 1/2 ("FieldTimeDerivative")^2 "LagrangianSecondFieldVelocityDerivative",
	"z2" -> 1/12 ("FieldTimeDerivative")^3 "LagrangianThirdFieldVelocityDerivative",
	"z" -> 1/("HubbleParameter") (("LagrangianThirdFieldVelocityDerivativeTimeDerivative")/("LagrangianThirdFieldVelocityDerivative")
			+ 3 ("FieldSecondTimeDerivative")/("FieldTimeDerivative")),
	"NonGaussianityAmplitude" -> 35/108 (1/("SpeedOfSound")^2 - 1)
			- 5/81 ((1/("SpeedOfSound")^2 - 1 - 2 ("z2")/("z1")) + (3 - 2 EulerGamma) "z" ("z2")/("z1"))
}];


(* ::Chapter::Closed:: *)
(*End*)


Protect @@ InflationSimulator`Private`$PublicSymbols;


End[];


EndPackage[];
