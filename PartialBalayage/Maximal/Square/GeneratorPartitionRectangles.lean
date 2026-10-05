/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles0
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles1
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles2
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles3
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles4
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles5
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles6
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles7
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles8
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRectangles9
public import PartialBalayage.Maximal.Square.Data.GeneratorPartitionRemainingRectangles

/-!
# Actual generator rectangle labels for checked coverage

The exact literal rectangles are assembled into a fixed finite label family.
Their identities as subdivision leaves are verified by ordinary kernel proofs
in the partition-tree modules.
-/

@[expose] public section

namespace PartialBalayage.Maximal.Square

set_option maxRecDepth 32768
set_option maxHeartbeats 0

/-- All explicitly labeled actual dyadic rectangles of the generator partition. -/
def generatorPartitionRectangles : Fin 106 → Fin 64 → GeneratorRectangle := ![
  generatorPartitionRectangles0,
  generatorPartitionRectangles1,
  generatorPartitionRectangles2,
  generatorPartitionRectangles3,
  generatorPartitionRectangles4,
  generatorPartitionRectangles5,
  generatorPartitionRectangles6,
  generatorPartitionRectangles7,
  generatorPartitionRectangles8,
  generatorPartitionRectangles9,
  generatorPartitionRectangles10,
  generatorPartitionRectangles11,
  generatorPartitionRectangles12,
  generatorPartitionRectangles13,
  generatorPartitionRectangles14,
  generatorPartitionRectangles15,
  generatorPartitionRectangles16,
  generatorPartitionRectangles17,
  generatorPartitionRectangles18,
  generatorPartitionRectangles19,
  generatorPartitionRectangles20,
  generatorPartitionRectangles21,
  generatorPartitionRectangles22,
  generatorPartitionRectangles23,
  generatorPartitionRectangles24,
  generatorPartitionRectangles25,
  generatorPartitionRectangles26,
  generatorPartitionRectangles27,
  generatorPartitionRectangles28,
  generatorPartitionRectangles29,
  generatorPartitionRectangles30,
  generatorPartitionRectangles31,
  generatorPartitionRectangles32,
  generatorPartitionRectangles33,
  generatorPartitionRectangles34,
  generatorPartitionRectangles35,
  generatorPartitionRectangles36,
  generatorPartitionRectangles37,
  generatorPartitionRectangles38,
  generatorPartitionRectangles39,
  generatorPartitionRectangles40,
  generatorPartitionRectangles41,
  generatorPartitionRectangles42,
  generatorPartitionRectangles43,
  generatorPartitionRectangles44,
  generatorPartitionRectangles45,
  generatorPartitionRectangles46,
  generatorPartitionRectangles47,
  generatorPartitionRectangles48,
  generatorPartitionRectangles49,
  generatorPartitionRectangles50,
  generatorPartitionRectangles51,
  generatorPartitionRectangles52,
  generatorPartitionRectangles53,
  generatorPartitionRectangles54,
  generatorPartitionRectangles55,
  generatorPartitionRectangles56,
  generatorPartitionRectangles57,
  generatorPartitionRectangles58,
  generatorPartitionRectangles59,
  generatorPartitionRectangles60,
  generatorPartitionRectangles61,
  generatorPartitionRectangles62,
  generatorPartitionRectangles63,
  generatorPartitionRectangles64,
  generatorPartitionRectangles65,
  generatorPartitionRectangles66,
  generatorPartitionRectangles67,
  generatorPartitionRectangles68,
  generatorPartitionRectangles69,
  generatorPartitionRectangles70,
  generatorPartitionRectangles71,
  generatorPartitionRectangles72,
  generatorPartitionRectangles73,
  generatorPartitionRectangles74,
  generatorPartitionRectangles75,
  generatorPartitionRectangles76,
  generatorPartitionRectangles77,
  generatorPartitionRectangles78,
  generatorPartitionRectangles79,
  generatorPartitionRectangles80,
  generatorPartitionRectangles81,
  generatorPartitionRectangles82,
  generatorPartitionRectangles83,
  generatorPartitionRectangles84,
  generatorPartitionRectangles85,
  generatorPartitionRectangles86,
  generatorPartitionRectangles87,
  generatorPartitionRectangles88,
  generatorPartitionRectangles89,
  generatorPartitionRectangles90,
  generatorPartitionRectangles91,
  generatorPartitionRectangles92,
  generatorPartitionRectangles93,
  generatorPartitionRectangles94,
  generatorPartitionRectangles95,
  generatorPartitionRectangles96,
  generatorPartitionRectangles97,
  generatorPartitionRectangles98,
  generatorPartitionRectangles99,
  generatorPartitionRectangles100,
  generatorPartitionRectangles101,
  generatorPartitionRectangles102,
  generatorPartitionRectangles103,
  generatorPartitionRectangles104,
  generatorPartitionRectangles105
]

end PartialBalayage.Maximal.Square
