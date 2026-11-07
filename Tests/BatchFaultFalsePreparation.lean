import Example.Tenant.S6bProofs
open Example.Tenant
example : BatchFault.PreparedEvidence S6bProofs.request S6bProofs.emptyPreparation := by
  constructor
  · left
    constructor
    · rfl
    · intro row member; cases member
  · intro index; exact Fin.elim0 index
