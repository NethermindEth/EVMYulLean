import EvmYul.State.Transaction

namespace EvmYul

def Transaction.to? : Transaction → Option AccountAddress
  | .legacy t | .access t | .dynamic t => t.recipient

def Transaction.data : Transaction → ByteArray
  | .legacy t | .access t | .dynamic t => t.data

end EvmYul
