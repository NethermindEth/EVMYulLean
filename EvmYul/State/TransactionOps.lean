import EvmYul.State.Transaction

namespace EvmYul

def Transaction.to? : Transaction → Option AccountAddress
  -- TODO: Blob transactions can never have `to`
  | .legacy t | .access t | .dynamic t | .blob t => t.recipient

def Transaction.data : Transaction → ByteArray
  | .legacy t | .access t | .dynamic t | .blob t => t.data

end EvmYul
