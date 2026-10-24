------------------------------------------------------------------------
-- Default uniform embedding family for the FinCat n tower
--
-- Constructs default-unif from the tower's structural facts
-- (nTower-retract and nTower-collapsible), applies surj to obtain
-- SurjectivityForTower, and assembles the unconditional universal limit
-- and non-triviality witness. The parameter m encodes n = suc (suc m),
-- so n ≥ 2 holds definitionally
--
-- FinCat n 塔的默认一致嵌入族
--
-- 从塔的结构事实（nTower-retract 与 nTower-collapsible）构造
-- default-unif，应用 surj 得到 SurjectivityForTower，
-- 并组装无条件的通用极限与非平凡见证。参数 m 编码 n = suc (suc m)，
-- 使 n ≥ 2 定义性成立
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNDefaultUnif where

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (ℕ)

open import SecondPass.CumulativeHierarchy using (mkEmbeddingData)
open import SecondPass.FinCatNTowerLemmas
open import SecondPass.FinCatNColimitWithDep
open import SecondPass.FinCatNSurjectivity

-- Parameterised construction over FinCatN m
-- FinCatN m 上的参数化构造
module FinCatNDefaultUnif (m : ℕ) where

  open FinCatNTowerLemmas m
  open FinCatNColimitWithDep m
    using (UniformEmbeddingFamilyForTower; SurjectivityForTower; UniversalLimitDep
          ; NontrivialLimitDep; dependentUniversalLimitDep; dependentNontrivialDep)
  open FinCatNSurjectivity m using (surj)

  -- Default uniform family: retraction from nTower-retract, collapsibility
  -- from nTower-collapsible, next-consistent by refl
  -- 默认一致族：收缩来自 nTower-retract，可坍缩性来自
  -- nTower-collapsible，next-consistent 由 refl 得证
  default-unif : UniformEmbeddingFamilyForTower
  default-unif k = record
    { family = record
        { getData = mkEmbeddingData (nTower-retract k) (nTower-collapsible k) }
    ; next-consistent = λ _ _ → refl
    }

  -- Surjectivity for the default family, from the unconditional surj
  -- 默认族的满射性，由无条件的 surj 给出
  surj-default : SurjectivityForTower default-unif
  surj-default = surj default-unif

  -- Unconditional universal limit over the default family
  -- 默认族上无条件的通用极限
  dependentUniversalLimit-default : UniversalLimitDep default-unif
  dependentUniversalLimit-default = dependentUniversalLimitDep default-unif surj-default

  -- Unconditional non-triviality witness over the default family
  -- 默认族上无条件的非平凡见证
  dependentNontrivial-default : NontrivialLimitDep dependentUniversalLimit-default
  dependentNontrivial-default = dependentNontrivialDep default-unif surj-default
