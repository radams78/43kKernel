## TODO

4. If r : Region then r.boundaryProof() outputs a proof that r.myBoundary.toCoq() = boundary r.toCoq()
5. Define signature : Region -> Signature
6. If r : Region then r.signatureProof() outputs a proof that r.getSignature().toCoq() = siganture r.toCoq()
1. Define size : Region -> nat
1. If r : Region then r.sizeProof() outputs a proof that r.size = size r.toCoq()
2. Write X.toCoq() for each subclass X of Region
7. Move on to SignatureTranscript