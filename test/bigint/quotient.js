const chai = require("chai");
const path = require("path");
const snarkjs = require("snarkjs");
const bigInt = require("big-integer");

const compiler = require("circom");


const assert = chai.assert;
chai.should();

function splitToWords(x, w, n, name) {
    let t = bigInt(x);
    w = bigInt(w);
    n = bigInt(n);
    const words = {};
    for (let i = 0; i < n; ++i) {
        words[`${name}[${i}]`] = `${t.mod(bigInt(2).pow(w))}`;
        t = t.divide(bigInt(2).pow(w));
    }
    if (!t.isZero()) {
        throw `Number ${x} does not fit in ${w * n} bits`;
    }
    return words;
}

function assertWitnessHas(circuit, witness, name, x, w, b) {
    let words = splitToWords(x, w, b, `main.${name}`);
    for (let [signal, value] of Object.entries(words)) {
        if (!witness[circuit.signalName2Idx[signal]].equals(snarkjs.bigInt(value))) {
            console.log(`${witness[circuit.signalName2Idx[signal]]} =?= ${(snarkjs.bigInt(value))}`);
        }
        assert(witness[circuit.signalName2Idx[signal]].equals(snarkjs.bigInt(value)));
    }
}
/*
describe("Quotient", () => {

    var circuit;
    var p = bigInt("12746234439581401046469859226373396085467258615645934830658503207936609828488753918578045873969432798202650853704567776318953671236706396322111794794094487");

    before(async () => {
        const cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "quotient_64bit_8word.circom"));
        circuit = new snarkjs.Circuit(cirDef);
    });

    it("should have at most 3n(w + 2) constraints (64 bits, 8 words)", async () => {
        // 3n(w+2) - 2
        // 3 * 8 * (64 + 3) - 2 = 1604
        circuit.nConstraints.should.be.at.most(1604);
    });

    it("should compute 0 %,/ p = 0,0 (64 bits, 8 words)", async () => {
        const witness = circuit.calculateWitness(
            Object.assign({},
                splitToWords(p, 64, 8, "divisor"),
                splitToWords(0, 64, 16, "dividend"))
        );
        assertWitnessHas(circuit, witness, "quotient", 0, 64, 8);
        assertWitnessHas(circuit, witness, "remainder", 0, 64, 8);
    });

    it("should compute p %,/ p = 1,0 (64 bits, 8 words)", async () => {
        const witness = circuit.calculateWitness(
            Object.assign({},
                splitToWords(p, 64, 16, "dividend"),
                splitToWords(p, 64, 8, "divisor"),
            )
        );
        assertWitnessHas(circuit, witness, "quotient", 1, 64, 8);
        assertWitnessHas(circuit, witness, "remainder", 0, 64, 8);
    });

    it("should compute p + 19 %,/ p = 1,19 (64 bits, 8 words)", async () => {
        const input = Object.assign({},
            splitToWords(bigInt(p).plus(bigInt(19)), 64, 16, "dividend"),
            splitToWords(p, 64, 8, "divisor"),
        );
        const witness = circuit.calculateWitness(input);
        assertWitnessHas(circuit, witness, "quotient", 1, 64, 8);
        assertWitnessHas(circuit, witness, "remainder", 19, 64, 8);
    });

    it("should compute p*p - 6 %,/ p = p-1,p-6 (64 bits, 8 words)", async () => {
        const input = Object.assign({},
            splitToWords(p.times(p).minus(bigInt(6)), 64, 16, "dividend"),
            splitToWords(p, 64, 8, "divisor"),
        );
        const witness = circuit.calculateWitness(input);
        assertWitnessHas(circuit, witness, "quotient", p.minus(bigInt(1)), 64, 8);
        assertWitnessHas(circuit, witness, "remainder", p.minus(bigInt(6)), 64, 8);
    });

    it("should compute p*p + p + 42 = (p + 1)p + (42) (64 bits, 8 words)", async () => {
        const input = Object.assign({},
            splitToWords(p.times(p).plus(bigInt(42)).plus(p), 64, 16, "dividend"),
            splitToWords(p, 64, 8, "divisor"),
        );
        const witness = circuit.calculateWitness(input);
        assertWitnessHas(circuit, witness, "quotient", p.plus(bigInt(1)), 64, 8);
        assertWitnessHas(circuit, witness, "remainder", bigInt(42), 64, 8);
    });

    it("should compute p*p = (p + 1)(p - 1) + (1) (64 bits, 8 words)", async () => {
        const input = Object.assign({},
            splitToWords(p.times(p), 64, 16, "dividend"),
            splitToWords(p.minus(1), 64, 8, "divisor"),
        );
        const witness = circuit.calculateWitness(input);
        assertWitnessHas(circuit, witness, "quotient", p.plus(bigInt(1)), 64, 8);
        assertWitnessHas(circuit, witness, "remainder", bigInt(1), 64, 8);
    });
});*/

describe("MultiplierReducer", () => {

    var circuit;
    var sC;
    var p = bigInt("28858049957327219110475323466896801383139428311490629626008833393729796965629869137141273938321966943265917767281641074671271164786944319433890041991406093028515386716990782181793093761129067169305130155891242986890110284754334115449064356078790445000930712254780776579648566779318075923514638583031243909381396976164215161751778856434764137856873712640342791431529842040087813072345501283466371742554216242409654188386730117931624242997459892740286011373140180679837723682252801483919461174828068240158469893453995167058545754659032707585919584523426981614564441078850910647537364925639054970775849977074598368946343");

    before(async () => {
        circuit = new snarkjs.Circuit(await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_reduce_2048.circom")));
        sC = new snarkjs.Circuit(await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_reduce_256.circom")));
    });

    it("should have at most (4n - 2)(w + 2) - 1 constraints (2048bits, 64/chunk)", async () => {
        // (4n - 1)(w + 2) - 1
        //  = (128 - 2)(68) - 1
        //  = 8635
        circuit.nConstraints.should.be.at.most(8567);
    });

    it("should have at most (4n - 2)(w + 2) - 1 constraints (256bits, 64/chunk)", async () => {
        // (4n - 1)(w + 2) - 1
        //  = (16 - 2)(68) - 1
        //  = 951
        sC.nConstraints.should.be.at.most(951);
    });

    it("should compute 0 * 0 % p = 0 (2048bits, 64/chunk)", async () => {
        const witness = circuit.calculateWitness(
            Object.assign({},
                splitToWords(0, 64, 32, "a"),
                splitToWords(0, 64, 32, "b"),
                splitToWords(p, 64, 32, "modulus"),
            )
        );
        assertWitnessHas(circuit, witness, "prod", 0, 64, 32);
    });

    it("should compute p * 1 % p = 0 (2048bits, 64/chunk)", async () => {
        const witness = circuit.calculateWitness(
            Object.assign({},
                splitToWords(p, 64, 32, "a"),
                splitToWords(1, 64, 32, "b"),
                splitToWords(p, 64, 32, "modulus"),
            )
        );
        assertWitnessHas(circuit, witness, "prod", 0, 64, 32);
    });

    it("should compute (p - 1) * (p - 1) % p = 1 (2048bits, 64/chunk)", async () => {
        const input =
            Object.assign({},
                splitToWords(p.minus(1), 64, 32, "a"),
                splitToWords(p.minus(1), 64, 32, "b"),
                splitToWords(p, 64, 32, "modulus"),
            );
        const witness = circuit.calculateWitness(input);
        assertWitnessHas(circuit, witness, "prod", 1, 64, 32);
    });

    it("should compute (p - 1) * (p - 2) % p = 2 (2048bits, 64/chunk)", async () => {
        const input =
            Object.assign({},
                splitToWords(p.minus(1), 64, 32, "a"),
                splitToWords(p.minus(2), 64, 32, "b"),
                splitToWords(p, 64, 32, "modulus"),
            );
        const witness = circuit.calculateWitness(input);
        assertWitnessHas(circuit, witness, "prod", 2, 64, 32);
    });
});
