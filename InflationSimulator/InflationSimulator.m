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
	InflationProperty, InflationPropertyData, InflationValue, InflatonLagrangianValue,
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


Options[InflationEvolution] = Join[{
	"FinalDensityPrecisionGoal" -> 1.*^-8,
	"FinalDensityRelativeDuration" -> 0.5,
	"ZeroDensityTolerance" -> 10,
	"MaxIntegrationTime" -> \[Infinity]
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
			{time -> 0},
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
					If[finalDensityPrecisionGoal > 0 &&
							finalDensity[time] - density <=
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
			DiscreteVariables -> {finalDensity, finalDensityStartTime},
			FilterRules[{o}, Options[NDSolve]],
			MaxSteps -> Infinity]];
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


InflationEvolution[lagrangian_, initialConditions_, time_, o : OptionsPattern[]] :=
	InflationEvolution[lagrangian, {initialConditions}, time, o]


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


InflationValue[
		lagrangian_,
		evolution_Association,
		time_,
		pivotEfoldings_,
		expression_,
		timespec_List] := Module[{
			fields, higherDerivativesRules, $D,
			evolutionVariablesOnly, propagatedDerivatives, trajectoryOnly,
			trajectoryOnlyNoTime},
	fields = Keys[evolution][[
			1 ;; (Position[Keys[evolution], "Efoldings"][[1, 1]] - 1) / 2]];
	
	evolutionVariablesOnly = expression //. $DerivedValues;
	
	propagatedDerivatives = evolutionVariablesOnly /.
		With[{variables = Append[fields, "Efoldings"]}, Join[
			Thread[variables -> Through[variables[time]]],
			Derivative[n_][#] :> $D[#[time], {time, n}] & /@ variables]] //.
		Derivative[n_][f_] :> $D[f, {time, n}] /.
		$D -> D;
		
	higherDerivativesRules = Append[
		With[{secondDerivatives = $FieldsSecondTimeDerivatives[
				lagrangian, Through[fields[time]], D[Through[fields[time]], time]]},
			Thread[Derivative[n_ ? (# >= 2 &)][#][time] & /@ fields :>
				Evaluate[D[#, {time, n - 2}] & /@ secondDerivatives]]],
		With[{efoldingsDerivative = $EfoldingsTimeDerivative[
				lagrangian, Through[fields[time]], D[Through[fields[time]], time]]},
			Derivative[n_ ? (# >= 1 &)]["Efoldings"][time] :>
				Evaluate[D[efoldingsDerivative, {time, n - 1}]]]];
	trajectoryOnly = propagatedDerivatives //. higherDerivativesRules;
	trajectoryOnlyNoTime = trajectoryOnly /. n_[time] :> n;
	
	Switch[#,
		_ ? NumericQ,
			trajectoryOnlyNoTime /. Join[
				Evaluate /@ (evolution /. x_InterpolatingFunction :> x[#]),
				<|time -> #|>],
		Indeterminate | Infinity | Missing[___],
			#,
		_,
			trajectoryOnly /. {time -> #}] & /@ (timespec /. {
			"HorizonExit" -> CosmologicalHorizonExitTime[evolution, pivotEfoldings],
			"Start" -> 0,
			"End" -> evolution["IntegrationTime"]})
]


InflationValue[
		lagrangian_,
		evolution_Association,
		time_,
		pivotEfoldings_,
		expression_,
		timespec_] :=
	InflationValue[
		lagrangian, evolution, time, pivotEfoldings, expression, {timespec}][[1]]


Options[InflationValue] = Options[InflationEvolution];


InflationValue[
		lagrangian_,
		initialConditions_,
		time_,
		pivotEfoldings_,
		expression_,
		timespec_,
		o : OptionsPattern[]] :=
	InflationValue[
		lagrangian,
		InflationEvolution[lagrangian, initialConditions, time, o],
		time,
		pivotEfoldings,
		expression,
		timespec]


(* ::Subsubsection:: *)
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


(* ::Subsection:: *)
(*InflatonLagrangianValue*)


InflatonLagrangianValue::nonq = "Only quadratic forms are supported for kinetic terms.";


InflatonLagrangianValue[lagrangian_, time_, expression_, state : {___List}] := Module[{
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


InflatonLagrangianValue[lagrangian_, time_, expression_, state_] :=
	InflatonLagrangianValue[lagrangian, time, expression, {state}]


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
