(* ::Package:: *)

(* ::Title:: *)
(*Inflation Simulator*)


(* ::Chapter::Closed:: *)
(*Begin*)


(* ::Text:: *)
(*See on GitHub: https://github.com/maxitg/InflationSimulator.*)


BeginPackage["InflationSimulator`"];


InflationSimulator`Private`$PublicSymbols = Hold[{
	InflatonDensity, InflatonPressure, InflationEquationsOfMotion,
	InflationEvolution, InflationStopsQ, InflationEfoldingsCount,
		CosmologicalHorizonExitTime, InflationQ,
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


InflationEvolution::nnuml = "Lagrangian did not evaluate to a numerical value.";


InflationEvolution::inwp =
	"Insufficient working precision. Doubling working precision to `1`.";


InflationEvolution::wpe =
	"Working precision `1` is too large. Increase MaxWorkingPrecision.";


InflationEvolution::comp =
	"Right-hand side of either Euler-Lagrange or Friedmann equation evaluated " <>
	"to a complex number.";


InflationEvolution::mff =
	"FieldFinal is implemented only for a single-field inflation.";


(* ::Subsubsection:: *)
(*Options*)


Options[InflationEvolution] = {
	"EfoldingsDerivativeThreshold" -> 16^^0.1,
	"EfoldingsThreshold" -> 16^^1000,
	"FieldDerivativeThreshold" -> 16^^0.01,
	"FieldBounceThreshold" -> 16^^20,
	"FieldFinal" -> Automatic,
	"MaxIntegrationTime" -> \[Infinity],
	WorkingPrecision -> Automatic,
	"MaxWorkingPrecision" -> ,
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
		inputFieldSpecs_,
		(*{field_, inputFieldInitial_ ? NumericQ,
				inputFieldDerivativeInitial_ ? NumericQ},*)
		time_,
		o : OptionsPattern[]] := Module[{
			workingPrecision, lagrangian, fieldSpecs, lagrangianNumericQ,
			fieldsValues, fieldsDerivativesValues, efoldingsValues, bounceValue,
				debugPrint,
			evolution, t, f, ft, n, fieldBounceCount, inflationStoppedQ,
				fieldVariables, fieldDerivativeVariables},
	workingPrecision = If[OptionValue[WorkingPrecision] === Automatic,
		MachinePrecision,
		OptionValue[WorkingPrecision]];
	If[workingPrecision >= 16 MachinePrecision,
		];
	{lagrangian, fieldSpecs} = $SetDoublePrecision[
			{inputLagrangian, inputFieldSpecs},
			OptionValue[WorkingPrecision]] /. Flatten @ Table[{
				D[field[time], time] -> ft[field][t],
				field[time] -> f[field][t]}, {field, inputFieldSpecs[[All, 1]]}];
	(* spec is {fieldLabel, initialValue, initialDerivativeValue} *)
	lagrangianNumericQ = Quiet[NumericQ[lagrangian /. Flatten @ Table[
		{ft[spec[[1]]][t] -> spec[[3]], f[spec[[1]]][t] -> spec[[2]]},
		{spec, inputFieldSpecs}]]];
	If[!lagrangianNumericQ, Message[InflationEvolution::nnuml]];
	If[OptionValue["Debug"],
		fieldsValues = Table[{}, fieldSpecs];
		fieldsDerivativesValues = Table[{}, fieldSpecs];
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
					FrameLabel -> {"Time", #[[2]]}] & /@ Append[
						Flatten @ Table[
							{{fieldsValues[[k]], fieldSpecs[[k, 1]]},
							 {fieldsDerivativesValues[[k]],
								 "\[PartialD]" <> fieldSpecs[[k, 1]]}},
							{k, Length @ fieldSpecs}],
						{efoldingsValues, "Efoldings"}]),
				ImageSize -> Scaled[1]]
		}], UpdateInterval -> 1]]];
	];
	fieldVariables = Table[f[field][t], {field, fieldSpecs[[All, 1]]}];
	fieldDerivativeVariables = Table[ft[field][t], {field, fieldSpecs[[All, 1]]}];
	
	With[{messagesToCatch = {
			Power::infy, Infinity::indet, Divide::indet, NDSolve::nlnum,
			NDSolve::nrnum1, NDSolve::ndcf, NDSolve::evcvmit, NDSolve::ndnum,
			Greater::nord, General::munfl, NDSolve::ndsz, NDSolve::nderr,
			InflationEvolution::comp}},
		Quieeet[Check[
			evolution = Join[Association[(With[{
					fieldStoppedCondition =
						t Sqrt[Total[fieldDerivativeVariables^2]] <
							Sqrt[Total[(fieldVariables - fieldSpecs[[All, 2]])^2]]
								OptionValue["FieldDerivativeThreshold"]},
				NDSolve[Join[
					Table[f[spec[[1]]][0] == spec[[2]], {spec, fieldSpecs}],
					Table[ft[spec[[1]]][0] == spec[[3]], {spec, fieldSpecs}],
					Table[f[field]'[t] == ft[field][t], {field, fieldSpecs[[All, 1]]}],
					Thread[Table[ft[field]'[t], {field, fieldSpecs[[All, 1]]}] ==
						$FieldsSecondTimeDerivatives[
							lagrangian, fieldVariables, fieldDerivativeVariables]],
					{n'[t] == $EfoldingsTimeDerivative[
						lagrangian, fieldVariables, fieldDerivativeVariables],
					 n[0] == 0,
					 fieldBounceCount[0] == 0},
					
					(* encountered complex field *)
					Table[With[{field = field}, WhenEvent[Im[f[field][t]] != 0,
						Message[InflationEvolution::comp];
						"StopIntegration",
						"LocationMethod" -> "StepEnd"
					]], {field, fieldSpecs[[All, 1]]}],
					
					(* efoldings stopped increasing *)
					{WhenEvent[t n'[t] <
								n[t] OptionValue["EfoldingsDerivativeThreshold"],
						inflationStoppedQ = True;
						"StopIntegration",
						"LocationMethod" -> "StepEnd"]},
						
					(* field stopped after max e-foldings reached *)
					{WhenEvent[fieldStoppedCondition,
						If[n[t] > OptionValue["EfoldingsThreshold"], 
							inflationStoppedQ = False;
							"StopIntegration"],
						"LocationMethod" -> "StepEnd"]},
					
					(* max e-foldings reached after field stopped *)
					{WhenEvent[n[t] > OptionValue["EfoldingsThreshold"],
						If[fieldStoppedCondition, 
							inflationStoppedQ = False;
							"StopIntegration"
						],
						"LocationMethod" -> "StepEnd"]},
						
					(* field bounced *)
					Table[With[{fieldDerivative = fieldDerivative},
						WhenEvent[fieldDerivative == 0,
							If[fieldBounceCount[t] >=
									OptionValue["FieldBounceThreshold"] - 1,
								inflationStoppedQ = False; "StopIntegration",
								fieldBounceCount[t] ->
									fieldBounceCount[t] + 1 / Length[fieldVariables]
							],
							"LocationMethod" -> "StepEnd"
					]], {fieldDerivative, fieldDerivativeVariables}],
					
					(* final field *)
					If[NumericQ[OptionValue["FieldFinal"]],
						If[Length[fieldVariables] == 1,
							{WhenEvent[fieldVariables[[1]] ==
									OptionValue["FieldFinal"],
								inflationStoppedQ = True;
								"StopIntegration",
								"LocationMethod" -> "StepEnd"]},
							Message[InflationEvolution::mff];
							{}
						],
						{}
					]],
				Join[
					Table[f[field], {field, fieldSpecs[[All, 1]]}],
					Table[ft[field], {field, fieldSpecs[[All, 1]]}],
					{n, fieldBounceCount}
				],
				{t, 0, OptionValue["MaxIntegrationTime"]},
				MaxSteps -> Infinity,
				DiscreteVariables -> fieldBounceCount,
				WorkingPrecision -> workingPrecision,
				PrecisionGoal -> OptionValue[PrecisionGoal],
				If[OptionValue["Debug"],
					EvaluationMonitor :> (
						Do[
							AppendTo[fieldsValues[[k]], {t, fieldVariables[[k]]}],
							{k, Length[fieldVariables]}];
						Do[
							AppendTo[
								fieldsDerivativesValues[[k]],
								{t, fieldDerivativeVariables[[k]]}],
							{k, Length[fieldDerivativeVariables]}];
						AppendTo[efoldingsValues, {t, n[t]}];
						If[Length[efoldingsValues] > 1000,
							Do[
								fieldsValues[[k]] = Rest[fieldsValues[[k]]];
								fieldsDerivativesValues[[k]] =
									Rest[fieldsDerivativesValues[[k]]],
								{k, Length[fieldsValues]}];
							efoldingsValues = Rest[efoldingsValues]];
						bounceValue = fieldBounceCount[t];
					),
					{}
				]
			]] /. {
				HoldPattern[NDSolve[_, _, ___]] :> {
					f[_] :> $Failed,
					ft[_] :> $Failed,
					n -> $Failed,
					fieldBounceCount -> $Failed
				}
			})[[1]] /. {
				f[label_] :> label,
				ft[label_] :> D[label, time],
				n -> "Efoldings",
				fieldBounceCount -> "FieldBounceCount"
			}], <|"InflationStoppedQ" -> inflationStoppedQ|>];
			NotebookDelete[debugPrint];
			Message[InflationEvolution::inwp, 2 workingPrecision];
			inflationStoppedQ = False;	
			InflationEvolution[
					inputLagrangian,
					inputFieldSpecs,
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


(* ::Subsubsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
(*$ExplicitProperty*)


ClearAll[$EvaluateProperty];


$EvaluateProperty[InflationProperty[prop_String, time_, o : OptionsPattern[]]] :=
		$ExplicitProperty[prop, time, OptionValue[InflationProperty, o, Method]];


ClearAll[$ExplicitProperty];


$ExplicitProperty[prop_String, time_, Automatic] := $ExplicitProperty[prop, time]


(* ::Subsubsection::Closed:: *)
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
				explicitProperties, propertiesByTime, valuesByTime},
	explicitProperties = $EvaluateProperty /@ properties;
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
			Association[{Reverse[#]}] & /@
					Thread[explicitProperties -> explicitProperties[[All, 2]]],
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


(* ::Subsubsection::Closed:: *)
(*$AddToSet*)


ClearAll[$AddToSet];
$AddToSet[set_, items_List] := Union[If[ListQ[set], Join[set, items], items]];
$AddToSet[set_, item_] := $AddToSet[set, {item}]


(* ::Subsubsection::Closed:: *)
(*Time*)


(* ::Text:: *)
(*Time simply returns its argument.*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"Time"}];


$InflationValue[
		lagrangian_,
		field_,
		time_,
		evolution_Association,
		"Time",
		lookupTime_ ? NumericQ] :=
	lookupTime


(* ::Subsubsection::Closed:: *)
(*Elementary observables*)


(* ::Text:: *)
(*First, we evaluate trivial observables, which we have already computed as part of the evolution, i.e. the value of the field, e-foldings, and their derivatives.*)


InflationPropertyData[] = $AddToSet[
		InflationPropertyData[], {"Field", "FieldTimeDerivative", "Efoldings"}];


$InflationValue[
		lagrangian_,
		field_,
		time_,
		evolution_Association,
		property : "Field" | "FieldTimeDerivative" | "Efoldings",
		lookupTime_ ? NumericQ] :=
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


(* ::Subsubsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
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


(* ::Subsection::Closed:: *)
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
