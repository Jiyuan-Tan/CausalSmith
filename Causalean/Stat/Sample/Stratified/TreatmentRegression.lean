module
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Basic
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.CategoricalLaw
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.ClipBounds
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Concentration
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.DesignAlgebra
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.ObservedSupport
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Occupancy
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.OccupancyScalar
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Residual
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.ResidualWeights
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Risk
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.TreatmentMoments

/-!
# Finite categorical treatment regression

This module collects finite-sample design, occupancy, residual-noise, and
clipped-risk bounds for within-cell treatment regression under arbitrary finite
categorical covariate distributions. Empty cells and a zero design Gram are
totalized explicitly, while overlap is required only on cells with positive
population mass.
-/
