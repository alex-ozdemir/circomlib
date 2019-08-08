include "./rsa_acc.circom"
include "./mult.circom"
include "../eddsamimc.circom";
include "../bitify.circom";

template TxHash() {
    signal input fromX;         // Source pk.x
    signal input fromY;         // Source pk.y
    signal input toX;           // Dest   pk.x
    signal input toY;           // Dest   pk.y
    signal input amt;           // Amount
    signal input fromNo;        // Tx Number (for this source)

    signal output out;

    component txHash = MultiMiMC7(6,91);
    txHash.in[0] <== fromX;
    txHash.in[1] <== fromY;
    txHash.in[2] <== toX;
    txHash.in[3] <== toY; 
    txHash.in[4] <== amt;
    txHash.in[5] <== fromNo;
    txHash.out ==> out;
}

template BalanceHash(w) {
    signal input pkX;
    signal input pkY;
    signal input amt;
    signal input txNo;

    var outBits = 1024;

    var n = outBits \ w;

    signal output out[n];

    signal hash[4];
    component hasher[4];
    component hashDecomp[4];
    for (var i = 0; i < 4; ++i) {
        hasher[i] = MultiMiMC7(5,91);
        hasher[i].in[0] <== i;
        hasher[i].in[1] <== pkX;
        hasher[i].in[2] <== pkY;
        hasher[i].in[3] <== amt;
        hasher[i].in[4] <== txNo;
        hashDecomp[i] = Num2Bits_strict();
        hashDecomp[i].in <== hasher[i].out;
    }

    // We're going to build a 1024b number like this:
    //
    //
    //              1  bbbbbbb   bbbbbbb   bbbbbbb   bbbbbbb   00000              1
    // | leading one | h4 bits | h3 bits | h2 bits | h1 bits | zeros | trailing one |
    //
    // The leading one gaurantees 1024bit-ness, and the trailing 1 gaurantees oddness
    var nBitsInHashes = 254 * 4;
    var nTrailingZeros = outBits - nBitsInHashes - 2;

    var combination[n];

    combination[0] += 1;
    for (var i = 0; i < 4; ++i) {
        for (var j = 0; j < 254; ++j) {
            // Bit index into the output number pictured above
            var outI = (i * 254 + j + nTrailingZeros + 1);
            combination[outI \ w] += (2 ** (outI % w)) * hashDecomp[i].out[j];
        }
    }
    combination[n - 1] += (2 ** (w - 1));

    for (var i = 0; i < n; ++i) {
        out[i] <== combination[i];
    }

}

template RsaRollup(rsaBits, hashBits, nTx) {
    var w = 32;
    var nN = rsaBits \ w;
    var nL = hashBits \ w;

    // Public parameters
    signal input modulus[nN];

    signal input oldDigest[nN];
    signal input newDigest[nN];

    // Signed transanTxion
    signal input txFromX[nTx];       // Source pk.x
    signal input txFromY[nTx];       // Source pk.y
    signal input txToX[nTx];         // Dest   pk.x
    signal input txToY[nTx];         // Dest   pk.y
    signal input txAmt[nTx];         // Amount
    signal input txFromNo[nTx];      // Tx Number (for this source)

    signal private input R8x[nTx];   // Tx signature
    signal private input R8y[nTx];   // Tx signature
    signal private input S[nTx];     // Tx signature

    // From the provider
    signal private input txToNo[nTx];     // Tx Number (for this dest)
    signal private input txFromBal[nTx];// Pre-Tx balance (for this source)
    signal private input txToBal[nTx];  // Pre-Tx balance (for this dest)

    // Accumulator proof witnesses
    signal private input intDigest[nN];
    signal private input oldWitness[nN];
    signal private input newWitness[nN];

    signal oldMember[nTx][nL];       // H(pk.x, pk.y, amt, no)
    signal newMember[nTx][nL];       // H(pk.x, pk.y, amt, no)
    signal txDigest[nTx];            // Hash of transaction (for signing)
    signal challenge[nL];           // H(all inputs)


    // Verify Signatures
    component txHash[nTx];
    component sigVerifier[nTx];
    for (var i = 0; i < nTx; ++i) {
        txHash[i] = TxHash();
        txHash[i].fromX = txFromX[i];
        txHash[i].fromY = txFromY[i];
        txHash[i].toX = txToX[i];
        txHash[i].toY = txToY[i];
        txHash[i].amt = txAmt[i];
        txHash[i].fromNo = txFromNo[i];
        sigVerifier[i] = EdDSAMiMCVerifier();
        sigVerifier[i].enabled <== 1;
        sigVerifier[i].Ax <== txFromX[i];
        sigVerifier[i].Ay <== txFromY[i];
        sigVerifier[i].R8x <== R8x[i];
        sigVerifier[i].R8y <== R8y[i];
        sigVerifier[i].S <== S[i];
        sigVerifier[i].M <== txHash[i].out;
    }

    // TODO Semantically verify Tx

    // TODO Verify Tx signature
    // TODO Hash the leaves?

    // Verify accumulator changes
    component intDigestVerifier = RSAggVerifyDelta(w, nN, nL, nTx);
    component newDigestVerifier = RSAggVerifyDelta(w, nN, nL, nTx);
    for (var i = 0; i < nN; ++i) {
        intDigestVerifier.modulus[i]       <== modulus[i];
        intDigestVerifier.digestWith[i]    <== oldDigest[i];
        intDigestVerifier.digestWithout[i] <== intDigest[i];
        intDigestVerifier.witness[i]       <== oldWitness[i];

        newDigestVerifier.modulus[i]       <== modulus[i];
        newDigestVerifier.digestWith[i]    <== newDigest[i];
        newDigestVerifier.digestWithout[i] <== intDigest[i];
        newDigestVerifier.witness[i]       <== newWitness[i];
    }
    for (var i = 0; i < nL; ++i) {
        newDigestVerifier.challenge[i] <== challenge[i];
        intDigestVerifier.challenge[i] <== challenge[i];
    }
    for (var i = 0; i < nTx; ++i) {
        for (var j = 0; j < nL; ++j) {
            intDigestVerifier.member[i][j] <== oldMember[i][j];
            newDigestVerifier.member[i][j] <== newMember[i][j];
        }
    }

}
