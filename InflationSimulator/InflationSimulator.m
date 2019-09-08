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
	InflationEvolution, CosmologicalHorizonExitTime, InflationQ,
	InflationValue, InflationPropertyData,
	InflatonLagrangianValue, InflatonLagrangianPropertyData,
	ExperimentallyConsistentInflationQ}];


Unprotect @@@ InflationSimulator`Private`$PublicSymbols;
ClearAll @@@ InflationSimulator`Private`$PublicSymbols;


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
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\).
InflatonDensity[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"1\", \"TR\"]], \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"2\", \"TR\"]], \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"\[Ellipsis]\", \"TR\"]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields the density for a Lagrangian with multiple fields.";


ClearAll[$InflatonDensity];
$InflatonDensity[lagrangian_, fieldsDot_] :=
	-lagrangian + Total[D[lagrangian, #] # & /@ fieldsDot]


InflatonDensity[lagrangian_, fields_List, time_] :=
	$InflatonDensity[lagrangian, D[fields, time]]


InflatonDensity[lagrangian_, field_, time_] :=
	InflatonDensity[lagrangian, {field}, time]


(* ::Subsection::Closed:: *)
(*InflatonPressure*)


InflatonPressure::usage = "InflatonPressure[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields the pressure of a homogeneous field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)] with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\).
InflatonPressure[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"1\", \"TR\"]], \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"2\", \"TR\"]], \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"\[Ellipsis]\", \"TR\"]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields the pressure for a Lagrangian with multiple fields.";


InflatonPressure[lagrangian_, fields_, time_] := lagrangian


(* ::Subsection::Closed:: *)
(*InflationEquationsOfMotion*)


InflationEquationsOfMotion::usage = "InflationEquationsOfMotion[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"n\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields equations fully describing the evolution of " <>
"a field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\) with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\) in homogeneous and isotropic spacetime, where \!\(\*
StyleBox[\"n\", \"TI\"]\) is the number of e-foldings as a function of time \!\(\*
StyleBox[\"t\", \"TI\"]\).
InflationEquationsOfMotion[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"1\", \"TR\"]], \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"2\", \"TR\"]], \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"\[Ellipsis]\", \"TR\"]\)}, \!\(\*
StyleBox[\"n\", \"TI\"]\)[\!\(\*
StyleBox[\"t\", \"TI\"]\)], \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields the equations for a multiple field model.";


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


(* ::Subsection::Closed:: *)
(*InflationEvolution*)


(* ::Subsubsection:: *)
(*Usage*)


InflationEvolution::usage = "InflationEvolution[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields functions describing evolution of the field " <>
"and the number of e-foldings over time \!\(\*
StyleBox[\"t\", \"TI\"]\) for a model with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), starting with initial conditions \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\) for the field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\), as well as the total number of e-foldings, total time, " <>
"and the final density sign.
InflationEvolution[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {{\!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"1\", \"TR\"]], \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[
RowBox[{\"1\", \",\", \" \", \"0\"}], \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[
RowBox[{\"1\", \",\", \" \", \"0\"}], \"TR\"]]\)}, {\!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"2\", \"TR\"]], \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[
RowBox[{\"2\", \",\", \" \", \"0\"}], \"TR\"]]\), \!\(\*SubscriptBox[
StyleBox[\"\[PartialD]\", \"TI\"], 
StyleBox[\"t\", \"TI\"]]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[
RowBox[{\"2\", \",\", \" \", \"0\"}], \"TR\"]]\)}, \!\(\*
StyleBox[\"\[Ellipsis]\", \"TR\"]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\)] yields the same for a multiple field inflation.";


(* ::Subsubsection:: *)
(*Messages*)


InflationEvolution::nnuml =
	"Lagrangian did not evaluate to a numerical value for initial condition.";


(* ::Subsubsection:: *)
(*Options*)


Options[InflationEvolution] = Join[{
	"FinalDensityPrecisionGoal" -> 8,
	"FinalDensityRelativeDuration" -> 0.5,
	"ZeroDensityRelativeThreshold" -> Automatic,
	"MaxIntegrationTime" -> \[Infinity],
	"EndOfInflationCondition" -> Automatic,
	"MaxBounceCount" -> Infinity
}, Options[NDSolve]];


ClearAll[$InitialEfoldings, $InitialDensityFraction, $StoppedEarlyString];
$InitialEfoldings = 0.1;
$InitialDensityFraction = 0.99;
$StoppedEarlyMissing = Missing["Unknown", "Stopped before reaching final density."];


(* ::Subsubsection:: *)
(*Implementation*)


InflationEvolution[
		lagrangian_,
		initialConditions : {___List},
		time_,
		o : OptionsPattern[]] := Module[{
			initialLagrangian, initialDensity,
			fields, velocities, variableTransformationRules,
			scaledLagrangian, scaledDensity,
			scaledMaxTime,
			finalDensitySign, scaledSolution, solution, integrationTime,
			field, velocity, efoldings, finalDensity, finalDensityStartTime,
			bounces, i},
	{initialLagrangian, initialDensity} = {
		lagrangian,
		$InflatonDensity[
				lagrangian,
				D[Through[initialConditions[[All, 1]][time]], time]]} /. Join[
			Thread[Through[initialConditions[[All, 1]][time]] ->
				initialConditions[[All, 2]]],
			Thread[D[Through[initialConditions[[All, 1]][time]], time] ->
				initialConditions[[All, 3]]],
			{time -> 0}];
	If[!NumericQ[initialLagrangian],
		Message[InflationEvolution::nnuml]; Return[$Failed]];
	
	{fields, velocities} = Transpose @ Table[
		#[i][time] & /@ {field, velocity}, {i, initialConditions[[All, 1]]}];
	variableTransformationRules = Flatten @ Table[
		{i'[time] -> Sqrt[initialDensity] velocity[i][time],
			i[time] -> field[i][time]},
		{i, initialConditions[[All, 1]]}];
	scaledLagrangian = lagrangian / initialDensity /. variableTransformationRules;
	scaledDensity = $InflatonDensity[scaledLagrangian, velocities];
	
	scaledMaxTime = If[initialDensity <= 0.,
		finalDensitySign = Sign[initialDensity];
		0,
		finalDensitySign = $StoppedEarlyMissing;
		OptionValue["MaxIntegrationTime"] Sqrt[initialDensity]];
	
	scaledSolution = With[{
			finalDensityPrecision =
				10^(-OptionValue["FinalDensityPrecisionGoal"]),
			finalDensityRelativeDuration =
				OptionValue["FinalDensityRelativeDuration"],
			zeroDensityPrecision = Replace[
				OptionValue["ZeroDensityRelativeThreshold"],
				Automatic -> 10 10^(-OptionValue["FinalDensityPrecisionGoal"])],
			initialEfoldings = $InitialEfoldings,
			initialDensityFraction = $InitialDensityFraction,
			scaledDensity = scaledDensity,
			endOfInflationCondition = OptionValue["EndOfInflationCondition"] /.
				variableTransformationRules},
		NDSolve[
			Join[
				(* Initial conditions *)
				Table[field[i[[1]]][0] == i[[2]], {i, initialConditions}],
				Table[
					velocity[i[[1]]][0] == i[[3]] / Sqrt[initialDensity],
					{i, initialConditions}],
				{efoldings[0] == 0},
				{finalDensity[0] == initialDensity},
				{finalDensityStartTime[0] == 0},
				Table[
					bounces[i][0] == 0,
					{i, initialConditions[[All, 1]]}],
				
				(* Evolution equations *)
				Table[
					field[i]'[time] == velocity[i][time],
					{i, initialConditions[[All, 1]]}],
				Thread[Table[velocity[i]'[time], {i, initialConditions[[All, 1]]}] ==
					(* Re is needed to avoid warnings if negative density is reached,
					   integration is aborted in that case, so no incorrect results
					   are returned. *)
					Re[$FieldsSecondTimeDerivatives[
						scaledLagrangian, fields, velocities]]],
				{efoldings'[time] == Re[$EfoldingsTimeDerivative[
					scaledLagrangian, fields, velocities]]},
				
				(* Custom end condition *)
				{If[endOfInflationCondition =!= Automatic,
					WhenEvent[endOfInflationCondition,
						finalDensitySign = If[
							scaledDensity <= zeroDensityPrecision,
							0,
							+1];
						"StopIntegration",
						"LocationMethod" -> "StepEnd"],
					Nothing]},
				
				(* Initialize final density thresholds *)
				{WhenEvent[efoldings[time] >= initialEfoldings ||
						scaledDensity <= initialDensityFraction,
					{finalDensity[time], finalDensityStartTime[time]} ->
						{scaledDensity, time},
					"LocationMethod" -> "StepEnd"]},
				
				(* Reached time threshold, potential end-of-inflation *)
				{WhenEvent[time > finalDensityStartTime[time] /
						(1 - finalDensityRelativeDuration),
					If[finalDensityPrecision > 0 &&
							finalDensity[time] - scaledDensity <=
								finalDensityPrecision (1 - finalDensity[time]),
						(* density is stable, check sign and stop *)
						finalDensitySign = If[
							scaledDensity <= zeroDensityPrecision,
							0,
							+1];
						"StopIntegration",
						(* density is still changing, set new threshold *)
						{finalDensity[time], finalDensityStartTime[time]} ->
							{scaledDensity, time}],
					"LocationMethod" -> "StepEnd"]},
				 
				(* Reached negative density, abort *)
				{WhenEvent[scaledDensity < 0,
					finalDensitySign = -1;
					"StopIntegration",
					"LocationMethod" -> "StepEnd"]},
				
				(* Bounce counter, separate for each field *)
				If[OptionValue["MaxBounceCount"] == Infinity,
					{},
					Table[
						With[{i = i},
							WhenEvent[velocity[i][time] == 0,
								bounces[i][time] -> bounces[i][time] + 1,
								"LocationMethod" -> "StepEnd"]],
						{i, initialConditions[[All, 1]]}]],
				
				(* Termination by bounce count *)
				If[OptionValue["MaxBounceCount"] == Infinity,
					{},
					Table[
						With[{i = i},
							WhenEvent[
								bounces[i][time] == OptionValue["MaxBounceCount"],
								If[And @@ Table[
										bounces[j][time] >=
											OptionValue["MaxBounceCount"],
										{j, initialConditions[[All, 1]]}],
									finalDensitySign = If[
										scaledDensity <= zeroDensityPrecision,
										0,
										+1];
									"StopIntegration"
								],
								"LocationMethod" -> "StepEnd"]],
						{i, initialConditions[[All, 1]]}]]],
			Join[
				Table[field[i], {i, initialConditions[[All, 1]]}],
				Table[velocity[i], {i, initialConditions[[All, 1]]}],
				{efoldings}
			],
			{time, 0, scaledMaxTime},
			DiscreteVariables -> Join[
				{finalDensity, finalDensityStartTime},
				Table[bounces[i], {i, initialConditions[[All, 1]]}]],
			FilterRules[{o}, Options[NDSolve]],
			MaxSteps -> Infinity]];
	If[Head[scaledSolution] === NDSolve,
		$Failed, (* something is wrong with NDSolve inputs *)
		(* This uses internal structure of InterpolatingFunction, so it might
			break in the future *)
		solution = scaledSolution /.
			InterpolatingFunction[$1_, $2_, $3_, {$41_, $42_, $43_}, $5_] :>
				InterpolatingFunction[
					$1 / Sqrt[initialDensity], (* domain *)
					$2, (* some metadata *)
					$3 / Sqrt[initialDensity], (* timestamps *)
					{$41, (* values *)
						$42,
						Table[
							$43[[i]] If[EvenQ[i], Sqrt[initialDensity], 1],
							{i, Length[$43]}]},
					$5] /.
			(velocity[x_] ->
					InterpolatingFunction[$1_, $2_, $3_, {$41_, $42_, $43_}, $5_]) :>
				velocity[x] -> InterpolatingFunction[
					$1,
					$2,
					$3,
					{$41, $42, $43 Sqrt[initialDensity]},
					$5];
		integrationTime = (efoldings /. solution)[[1, 1, 1, 2]];
		Join[
			Association[solution[[1]] /. {
				field[label_] :> label,
				velocity[label_] :> label',
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


InflationEvolution[lagrangian_, initialConditions_, time_, o : OptionsPattern[]] :=
	InflationEvolution[lagrangian, {initialConditions}, time, o]


(* ::Subsection::Closed:: *)
(*CosmologicalHorizonExitTime*)


CosmologicalHorizonExitTime::usage = "CosmologicalHorizonExitTime[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"init\", \"TI\"]\), \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] yields the time at which a scale specified by " <>
"\!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\) exits cosmological horizon during inflation " <>
"produced by a model with Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), starting with initial conditions \!\(\*
StyleBox[\"init\", \"TI\"]\).
CosmologicalHorizonExitTime[\!\(\*
StyleBox[\"evo\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] takes the output \!\(\*
StyleBox[\"evo\", \"TI\"]\) of InflationEvolution as its input.";


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


(* ::Subsection::Closed:: *)
(*InflationQ*)


InflationQ::usage = "InflationQ[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"init\", \"TI\"]\), \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] yields True if inflation stops (final density " <>
"is zero) and produces at least \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\) number of e-foldings.
InflationQ[\!\(\*
StyleBox[\"evo\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] takes the output \!\(\*
StyleBox[\"evo\", \"TI\"]\) of InflationEvolution as its input.";


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


(* ::Subsection::Closed:: *)
(*InflationValue*)


(* ::Subsubsection:: *)
(*InflationValue implementation*)


InflationValue::usage = "InflationValue[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"init\", \"TI\"]\), \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\), \!\(\*
StyleBox[\"property\", \"TI\"]\), \!\(\*
StyleBox[\"timespec\", \"TI\"]\)] yields the value of a specified \!\(\*
StyleBox[\"property\", \"TI\"]\)\!\(\*
StyleBox[\" \", \"TI\"]\)at time \!\(\*
StyleBox[\"timespec\", \"TI\"]\) for a specified model.
InflationValue[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"evo\", \"TI\"]\), \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\), \!\(\*
StyleBox[\"property\", \"TI\"]\), \!\(\*
StyleBox[\"timespec\", \"TI\"]\)] yields the value using a precomputed output of " <>
"InflationEvolution \!\(\*
StyleBox[\"evo\", \"TI\"]\).";


Attributes[InflationValue] = {HoldAll};


InflationValue[lagrangian_,
		evolutionOrInitialConditions_,
		time_,
		pivotEfoldings_,
		expression_,
		timespec_,
		o : OptionsPattern[]] :=
	$InflationValue[lagrangian,
		evolutionOrInitialConditions,
		time,
		pivotEfoldings,
		Hold[expression],
		timespec,
		o]


$InflationValue[
		lagrangian_,
		evolution_Association,
		time_,
		pivotEfoldings_,
		expression_,
		timespec_List] := Module[{
			fields, variables, elementaryFunctions, timespecExplicit,
			variableValues, modelExpressions, modelValues,
			simplifiedExpression, substituteEvolutionDerivatives,
			$timeD, $timeDExpression, $fieldD, k},
	fields = Keys[evolution][[
			1 ;; (Position[Keys[evolution], "Efoldings"][[1, 1]] - 1) / 2]];
	variables = Append[fields, "Efoldings"];
	elementaryFunctions = Join[
		Through[fields[time]], D[Through[fields[time]], time], {"Efoldings"[time]}];
	
	timespecExplicit = timespec /. {
		"Start" -> 0,
		"HorizonExit" -> CosmologicalHorizonExitTime[evolution, pivotEfoldings],
		"End" -> evolution["IntegrationTime"]
	};
	
	variableValues = Association[
			Table[v -> evolution[Head @ v][#], {v, elementaryFunctions}]] &
		/@ timespecExplicit;
	modelExpressions = <|
		"Lagrangian" @@ elementaryFunctions -> lagrangian,
		"Density" @@ elementaryFunctions ->
			InflatonDensity[lagrangian, Through[fields[time]], time],
		"Pressure" @@ elementaryFunctions ->
			InflatonPressure[lagrangian, Through[fields[time]], time]|>;
	modelValues = modelExpressions /. # & /@ variableValues;
		
	simplifiedExpression = ReleaseHold[expression //. $DerivedValues
		//. Derivative[n_][k_] :> D[k, {time, n}]
		/. Thread[variables -> Through[variables[time]]]
		/. {l : "Lagrangian" | "Density" | "Pressure" :> l @@ elementaryFunctions}];
	
	substituteEvolutionDerivatives[k_][expr_] := expr
		/. variableValues[[k]]
		/. Derivative[order_][func_][time] :> $timeD[order, func, k]
		/. time -> timespecExplicit[[k]];
	
	$timeD[orders_, func_, k_] := $timeD[orders, func, k] =
		substituteEvolutionDerivatives[k][$timeDExpression[orders, func, k]];
	
	$timeDExpression[order_, "Efoldings", k_] :=
		D[
			$EfoldingsTimeDerivative[
				lagrangian,
				Through[fields[time]],
				D[Through[fields[time]], time]],
			{time, order - 1}];
	
	$timeDExpression[order_, field_, k_] := Module[{position},
		position = FirstPosition[Through[fields[time]], field][[1]];
		D[
			$FieldsSecondTimeDerivatives[
				lagrangian,
				Through[fields[time]],
				D[Through[fields[time]], time]][[position]],
			{time, order - 2}]
	];
	
	$fieldD[
			orders_,
			func : "Lagrangian" | "Density" | "Pressure",
			args_,
			k_] := $fieldD[orders, func, args, k] =
		substituteEvolutionDerivatives[k][
			D[func @@ args /. modelExpressions, ##] & @@ Transpose[{args, orders}]];
	
	Table[substituteEvolutionDerivatives[k][simplifiedExpression
		/. modelValues[[k]]
		/. Derivative[order__][func : "Lagrangian" | "Density" | "Pressure"][args__]
			:> $fieldD[{order}, func, {args}, k]], {k, Length[timespecExplicit]}]
]


$InflationValue[
		lagrangian_,
		evolution_Association,
		time_,
		pivotEfoldings_,
		expression_,
		timespec_] :=
	$InflationValue[
		lagrangian, evolution, time, pivotEfoldings, expression, {timespec}][[1]]


Options[InflationValue] = Options[$InflationValue] = Options[InflationEvolution];


$InflationValue[
		lagrangian_,
		initialConditions_,
		time_,
		pivotEfoldings_,
		expression_,
		timespec_,
		o : OptionsPattern[]] :=
	$InflationValue[
		lagrangian,
		InflationEvolution[lagrangian, initialConditions, time, o],
		time,
		pivotEfoldings,
		expression,
		timespec]


(* ::Subsubsection:: *)
(*InflationPropertyData*)


InflationPropertyData::usage = "InflationPropertyData[] " <>
"gives the list of all basic properties supported by InflationValue.";


(* ::Text:: *)
(*The values are added later in the implementation.*)


InflationPropertyData[] = {"Efoldings", "Lagrangian", "Density", "Pressure"};


(* ::Subsubsection::Closed:: *)
(*$AddToSet*)


ClearAll[$AddToSet];
$AddToSet[set_, items_List] := Union[If[ListQ[set], Join[set, items], items]];
$AddToSet[set_, item_] := $AddToSet[set, {item}]


(* ::Subsubsection:: *)
(*Hubble parameter*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"HubbleParameter"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"HubbleParameter" -> "Efoldings"'
}];


(* ::Subsubsection:: *)
(*Slow-roll parameter \[Epsilon]*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"SlowRollEpsilon"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollEpsilon" -> - "HubbleParameter"' / ("HubbleParameter")^2
}];


(* ::Subsubsection:: *)
(*Slow-roll parameter \[Eta]*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"SlowRollEta"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"SlowRollEta" -> "SlowRollEpsilon"' / ("SlowRollEpsilon" "HubbleParameter")
}];


(* ::Subsubsection:: *)
(*Effective axion decay constant*)


InflationPropertyData[] =
		$AddToSet[InflationPropertyData[], {"EffectiveAxionDecayConstant"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"EffectiveAxionDecayConstant" -> 1 / Sqrt["SlowRollEta" - 2 "SlowRollEpsilon"]
}];


(* ::Subsubsection:: *)
(*Scalar and tensor spectral indices*)


InflationPropertyData[] = $AddToSet[
		InflationPropertyData[], {"ScalarSpectralIndex", "TensorSpectralIndex"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"ScalarSpectralIndex" -> 1 - 2 "SlowRollEpsilon" - "SlowRollEta",
	"TensorSpectralIndex" -> - 2 "SlowRollEpsilon"
}];


(* ::Subsubsection:: *)
(*Tensor-to-scalar ratio*)


InflationPropertyData[] = $AddToSet[InflationPropertyData[], {"TensorToScalarRatio"}];


$DerivedValues = $AddToSet[$DerivedValues, {
	"TensorToScalarRatio" -> 16 "SlowRollEpsilon"
}];


(* ::Subsection::Closed:: *)
(*InflatonLagrangianValue*)


InflatonLagrangianValue::usage = "InflatonLagrangianValue[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {\!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*
StyleBox[\"property\", \"TI\"]\)] yields the value of a specified \!\(\*
StyleBox[\"property\", \"TI\"]\) of Lagrangian \!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\) of the field \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)\!\(\*
StyleBox[\"(\", \"TI\"]\)\!\(\*
StyleBox[\"t\", \"TI\"]\)\!\(\*
StyleBox[\")\", \"TI\"]\) assuming the field takes the value \!\(\*
StyleBox[\"\[CurlyPhi]\", \"TI\"]\)\!\(\*
StyleBox[\"=\", \"TI\"]\)\!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"0\", \"TR\"]]\).
InflatonLagrangianValue[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), {{\!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"1\", \"TR\"]], \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[
RowBox[{\"1\", \",\", \" \", \"0\"}], \"TR\"]]\)}, {\!\(\*
StyleBox[SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[\"2\", \"TR\"]], \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"\[CurlyPhi]\", \"TI\"], 
StyleBox[
RowBox[{\"2\", \",\", \" \", \"0\"}], \"TR\"]]\)}, \!\(\*
StyleBox[\"\[Ellipsis]\", \"TR\"]\)}, \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*
StyleBox[\"property\", \"TI\"]\)] yields the value of a specified \!\(\*
StyleBox[\"property\", \"TI\"]\) for a multiple field Lagrangian.";


InflatonLagrangianValue::nonq = "Only quadratic forms are supported for kinetic terms.";


InflatonLagrangianValue[lagrangian_, state : {___List}, time_, expression_] := Module[{
		fields, momenta, metric, potential, metricDerivative, connection},
	fields = Through[state[[All, 1]][time]];
	momenta = D[fields, time];
	metric = D[lagrangian, {momenta, 2}];
	If[(D[lagrangian, {momenta}] /. Thread[momenta -> 0]) !=
				Table[0, Length[momenta]] ||
			!And @@ (FreeQ[metric, #, All] & /@ momenta),
		Message[InflatonLagrangianValue::nonq]; Return[$Failed]];
	potential = - lagrangian /. Thread[momenta -> 0];
	metricDerivative = D[metric, {fields}];
	connection = 1/2 TensorContract[
		TensorProduct[
			Inverse[metric],
			metricDerivative
				+ Transpose[metricDerivative, 1 <-> 2]
				- Transpose[metricDerivative, 1 <-> 3]],
		{{1, 5}}];
	expression //. {
		"SlowRollEpsilon" :> (
			1/2 D[potential, {fields}].Inverse[metric].D[potential, {fields}]
					/ potential^2 /.
				Thread[fields -> state[[All, 2]]]),
		"SlowRollEta" -> (
			D[potential, {fields}]
						.Inverse[metric]
						.(D[potential, {fields, 2}]
							- D[potential, {fields}].connection)
						.Inverse[metric]
						.D[potential, {fields}] /
					(potential
						D[potential, {fields}]
						.Inverse[metric]
						.D[potential, {fields}]) /.
				Thread[fields -> state[[All, 2]]]),
		"EffectiveAxionDecayConstant" ->
			1 / Sqrt[2 ("SlowRollEpsilon" - "SlowRollEta")]
	}
]


InflatonLagrangianValue[lagrangian_, state_, time_, expression_] :=
	InflatonLagrangianValue[lagrangian, {state}, time, expression]


(* ::Subsection::Closed:: *)
(*InflatonLagrangianPropertyData*)


InflatonLagrangianPropertyData::usage = "InflatonLagrangianPropertyData[] " <>
"gives the list of all basic properties supported by InflatonLagrangianValue.";


InflatonLagrangianPropertyData[] =
	{"SlowRollEpsilon", "SlowRollEta", "EffectiveAxionDecayConstant"};


(* ::Section:: *)
(*Comparison with Experiment*)


(* ::Subsection::Closed:: *)
(*ExperimentallyConsistentInflationQ*)


ExperimentallyConsistentInflationQ::usage = "ExperimentallyConsistentInflationQ[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"init\", \"TI\"]\), \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] yields True if the specified model results in " <>
"inflation with experimentally consistent observables, and False otherwise.
ExperimentallyConsistentInflationQ[\!\(\*
StyleBox[\"\[ScriptCapitalL]\", \"TI\"]\), \!\(\*
StyleBox[\"evo\", \"TI\"]\), \!\(\*
StyleBox[\"t\", \"TI\"]\), \!\(\*SubscriptBox[
StyleBox[\"N\", \"TI\"], 
StyleBox[\"pivot\", \"TI\"]]\)] uses precomputed output of InflationEvolution \!\(\*
StyleBox[\"evo\", \"TI\"]\).
ExperimentallyConsistentInflationQ[\!\(\*SubscriptBox[
StyleBox[\"n\", \"TI\"], 
StyleBox[\"s\", \"TI\"]]\), \!\(\*
StyleBox[\"r\", \"TI\"]\)] yields True if a given index of scalar spectral " <>
"perturbations \!\(\*SubscriptBox[
StyleBox[\"n\", \"TI\"], 
StyleBox[\"s\", \"TI\"]]\) and tensor-to-scalar power spectrum ratio \!\(\*
StyleBox[\"r\", \"TI\"]\) are consistent with experimental bounds, and False " <>
"otherwise.";


Options[ExperimentallyConsistentInflationQ] = Options[InflationEvolution];


ClearAll[$PlanckScalarIndexTensorToScalarRatioRegion];
$PlanckScalarIndexTensorToScalarRatioRegion = Region @ Polygon @ Rest @ Import @
		PacletManager`PacletResource[
				"InflationSimulator", "PlanckConstraints-TT_TE_EE_lowP-95CL.csv"];


ExperimentallyConsistentInflationQ[ns_ ? NumericQ, r_ ? NumericQ] :=
	RegionMember[$PlanckScalarIndexTensorToScalarRatioRegion, {ns, r}]


ExperimentallyConsistentInflationQ[
		lagrangian_, evolution_Association, time_, pivotEfoldings_] :=
	InflationQ[evolution, pivotEfoldings] &&
		ExperimentallyConsistentInflationQ @@ InflationValue[
			lagrangian,
			evolution,
			time,
			pivotEfoldings,
			{"ScalarSpectralIndex", "TensorToScalarRatio"},
			"HorizonExit"]


ExperimentallyConsistentInflationQ[
		lagrangian_,
		initialConditions_,
		time_,
		pivotEfoldings_,
		o : OptionsPattern[]] :=
	ExperimentallyConsistentInflationQ[
		lagrangian,
		InflationEvolution[lagrangian, initialConditions, time, o],
		time,
		pivotEfoldings]


(* ::Chapter::Closed:: *)
(*End*)


Protect @@@ InflationSimulator`Private`$PublicSymbols;


End[];


EndPackage[];
