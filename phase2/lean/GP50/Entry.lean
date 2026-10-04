import GP50.Decoder
import GP50.Runtime
namespace GP50
-- Raw input must pass duplicate-key and typed validation before event resolution.
def decodeFold (admission : Admission) (text : String) : Except String RuntimeState := do
  fold admission (← Decoder.decode text)
end GP50
