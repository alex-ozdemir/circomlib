include "./bigint.circom"

template RabinVerifier(w, n) {
    // w * n is enough bits to store `sig`.
    // Constraints <= 
    // 2 multipliers and a 2048 bit split
    // For at most $2(2n(w + 3) - 2) + n(w+1)$ constraints.
    //             $n(5w + 13) - 4$            constraints

    // Checks: sig * sig == x * pk + msg

    signal input sig[n];
    signal input msg[n];
    signal input pk[n];

    signal input x[n];

    // Compute the x
    // Doesn't work because computation types are in F
    // compute {
    //     var sigAcc = 0;
    //     var msgAcc = 0;
    //     var pkAcc = 0;
    //     for (var i = 0; i < n; i++) {
    //         sigAcc += sig[i] << (w * i);
    //         msgAcc += msg[i] << (w * i);
    //         pkAcc  += pk[i]  << (w * i);
    //     }
    //     var xAcc = sigAcc;
    //     for (var i = 0; i < n; i++) {
    //         x[i] <-- xAcc % (2 ** w);
    //         xAcc = xAcc >> w;
    //     }
    // }

    // Verify the wordness of x lest our multipliers break
    component xBits[n];
    for (var i = 0; i < n; i++) {
        xBits[i] = Num2Bits(w);
        xBits[i].in <== x[i];
    }

    component left = LinearMultiplier(w, n);
    component right = LinearMultiplierWithAdd(w, n);

    for (var i = 0; i < n; i++) {
        left.a[i] <== sig[i];
        left.b[i] <== sig[i];
        right.a[i] <== x[i];
        right.b[i] <== pk[i];
        right.c[i] <== msg[i];
    }

    for (var i = 0; i < 2 * n; i++) {
        left.prod[i] === right.prod[i];
    }

}
