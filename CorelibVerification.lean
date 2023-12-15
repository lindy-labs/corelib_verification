import CorelibVerification.Corelib.Array
import CorelibVerification.Corelib.Hash
import CorelibVerification.Corelib.Integer
import CorelibVerification.Corelib.Lib
import CorelibVerification.Corelib.Result
import CorelibVerification.Corelib.Serde
import CorelibVerification.Corelib.Starknet.SyscallResult
import CorelibVerification.Corelib.Starknet.ContractAddress
import CorelibVerification.Corelib.Starknet.Info
import CorelibVerification.Corelib.Starknet.StorageAccess
import CorelibVerification.Corelib.Starknet

/- Trivial spec for the dummy function -/
aegis_spec "corelib_verification::main" :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True

aegis_prove "corelib_verification::main" :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro

aegis_complete
