(* ::Package:: *)

(* ::Title:: *)
(*Inflation Simulator*)


(* ::Chapter:: *)
(*Begin*)


(* ::Text:: *)
(*See on GitHub: https://github.com/maxitg/InflationSimulator.*)


BeginPackage["InflationSimulator`", {"UsageString`"}];


InflationSimulator`Private`$PublicSymbols = {
	InflatonDensity, InflatonPressure, InflationEquationsOfMotion,
	InflationEvolution, InflationStopsQ, InflationEfoldingsCount,
		CosmologicalHorizonExitTime, InflationQ};


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
Off[InflationEvolution::inwp];


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


(* ::Chapter::Closed:: *)
(*End*)


Protect @@ InflationSimulator`Private`$PublicSymbols;


End[];


EndPackage[];
