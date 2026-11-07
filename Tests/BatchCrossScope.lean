import Example.Tenant.S4bProofs
open Example.Tenant Example.Tenant.S4bProofs
example : Binding.taskProjectSingle request sharedTask () =
    Binding.taskProjectSingle otherRequest sharedTask () := by rfl
