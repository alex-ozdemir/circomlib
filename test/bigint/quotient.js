const chai = require("chai");
const path = require("path");
const snarkjs = require("snarkjs");
const bigInt = require("big-integer");

const compiler = require("circom");

const { splitToWords, assertWitnessHas, extractExpr } = require("./util.js");

chai.should();

describe("EqualWhenCarried", () => {
    var constraints = (w, n) => ((n - 1) * (w + 2 + Math.ceil(Math.log2(n))));
    var circuit;
    before(async () => {
        circuit = new snarkjs.Circuit(
            await compiler(
                path.join(__dirname, "..", "circuits", "bigint", "equal_when_carried_32bit_16word.circom")));
    });

    it(`should have ${constraints(32, 16)} = ${extractExpr(constraints)} constraints (2048b)`, async () => {
        const bound = constraints(32, 16);
        circuit.nConstraints.should.be.at.most(bound);
    });
});

describe("MultiplierReducer", () => {

    var constraints = (w, n) => (2 * n * (2*w + Math.ceil(Math.log2(n)) + 5) - 2*w - 7);
    var m2048;
    var m2048w32;
    var m2048w16;
    var m256;
    var bit12;
    var p = bigInt("28858049957327219110475323466896801383139428311490629626008833393729796965629869137141273938321966943265917767281641074671271164786944319433890041991406093028515386716990782181793093761129067169305130155891242986890110284754334115449064356078790445000930712254780776579648566779318075923514638583031243909381396976164215161751778856434764137856873712640342791431529842040087813072345501283466371742554216242409654188386730117931624242997459892740286011373140180679837723682252801483919461174828068240158469893453995167058545754659032707585919584523426981614564441078850910647537364925639054970775849977074598368946343");

    before(async () => {
        m2048 = new snarkjs.Circuit(await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_reduce_2048.circom")));
        m2048w32 = new snarkjs.Circuit(await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_reduce_2048_32b.circom")));
        m2048w16 = new snarkjs.Circuit(await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_reduce_2048_16b.circom")));
        m256 = new snarkjs.Circuit(await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_reduce_256.circom")));
        bit12 = new snarkjs.Circuit(await compiler(path.join(__dirname, "..", "circuits", "bigint", "mult_reduce_12.circom")));
    });

    it(`should have ${constraints(64, 32)} = ${extractExpr(constraints)} constraints (2048b, 64b words)`, async () => {
        const bound = constraints(64, 32);
        m2048.nConstraints.should.be.at.most(bound);
    });
    it("should have <= 5200 constraints (2048b, 32b words)", async () => {
        m2048w32.nConstraints.should.be.at.most(5200);
    });
    it("should have <= 5100 constraints (2048b, 16b words)", async () => {
        m2048w16.nConstraints.should.be.at.most(5100);
    });
    it(`should have ${constraints(64, 4)} = ${extractExpr(constraints)} constraints (256b)`, async () => {
        const bound = constraints(64, 4);
        m256.nConstraints.should.be.at.most(bound);
    });

    it("should compute 0 * 0 % p = 0 (2048bits, 64/chunk)", async () => {
        const witness = m2048.calculateWitness(
            Object.assign({},
                splitToWords(0, 64, 32, "a"),
                splitToWords(0, 64, 32, "b"),
                splitToWords(p, 64, 32, "modulus"),
            )
        );
        assertWitnessHas(m2048, witness, "prod", 0, 64, 32);
    });

    it("should compute p * 1 % p = 0 (2048bits, 64/chunk)", async () => {
        const witness = m2048.calculateWitness(
            Object.assign({},
                splitToWords(p, 64, 32, "a"),
                splitToWords(1, 64, 32, "b"),
                splitToWords(p, 64, 32, "modulus"),
            )
        );
        assertWitnessHas(m2048, witness, "prod", 0, 64, 32);
    });

    it("should compute (p - 1) * (p - 1) % p = 1 (2048bits, 64/chunk)", async () => {
        const input =
            Object.assign({},
                splitToWords(p.minus(1), 64, 32, "a"),
                splitToWords(p.minus(1), 64, 32, "b"),
                splitToWords(p, 64, 32, "modulus"),
            );
        const witness = m2048.calculateWitness(input);
        assertWitnessHas(m2048, witness, "prod", 1, 64, 32);
    });

    it("should compute (p - 1) * (p - 2) % p = 2 (2048bits, 64/chunk)", async () => {
        const input =
            Object.assign({},
                splitToWords(p.minus(1), 64, 32, "a"),
                splitToWords(p.minus(2), 64, 32, "b"),
                splitToWords(p, 64, 32, "modulus"),
            );
        const witness = m2048.calculateWitness(input);
        assertWitnessHas(m2048, witness, "prod", 2, 64, 32);
    });

    it("should compute (p - 1) * (p - 2) % p = 2 (2048bits, 64/chunk)", async () => {
        const input =
            Object.assign({},
                splitToWords(p.minus(1), 64, 32, "a"),
                splitToWords(p.minus(2), 64, 32, "b"),
                splitToWords(p, 64, 32, "modulus"),
            );
        const witness = m2048.calculateWitness(input);
        assertWitnessHas(m2048, witness, "prod", 2, 64, 32);
    });

    it("should compute 1 * 1 % N = 1 (12 bits, 4/chunk)", async () => {
        const N = bigInt(2 ** 11 + 2 ** 6);
        const input =
            Object.assign({},
                splitToWords(1, 4, 3, "a"),
                splitToWords(1, 4, 3, "b"),
                splitToWords(N, 4, 3, "modulus"),
            );
        const witness = bit12.calculateWitness(input);
        assertWitnessHas(bit12, witness, "prod", 1, 4, 3);
    });

    it("should compute (N - 1) * 2 % N = 2 (12 bits, 4/chunk)", async () => {
        const N = bigInt(2 ** 12 - 1 - 2 ** 10);
        const input =
            Object.assign({},
                splitToWords(N - 1, 4, 3, "a"),
                splitToWords(2, 4, 3, "b"),
                splitToWords(N, 4, 3, "modulus"),
            );
        const witness = bit12.calculateWitness(input);
        assertWitnessHas(bit12, witness, "prod", N - 2, 4, 3);
    });
    it("should compute (N - 1) * (N - 1) % N = 1 (12 bits, 4/chunk)", async () => {
        const N = bigInt(2 ** 12 - 1 - 2 ** 10);
        const input =
            Object.assign({},
                splitToWords(N - 1, 4, 3, "a"),
                splitToWords(N - 1, 4, 3, "b"),
                splitToWords(N, 4, 3, "modulus"),
            );
        const witness = bit12.calculateWitness(input);
        assertWitnessHas(bit12, witness, "prod", 1, 4, 3);
    });
    it("should compute with high-weight inputs (12 bits, 4/chunk)", async () => {
        const N = bigInt(2 ** 12 - 1 - 2 ** 10);
        const a = bigInt(2 ** 11 - 1);
        const b = bigInt(2 ** 11 - 1);
        const input =
            Object.assign({},
                splitToWords(a, 4, 3, "a"),
                splitToWords(b, 4, 3, "b"),
                splitToWords(N, 4, 3, "modulus"),
            );
        const witness = bit12.calculateWitness(input);
        const output = a.times(b).mod(N);
        assertWitnessHas(bit12, witness, "prod", output, 4, 3);
    });
    it("should compute with high-value, low-weight inputs (12 bits, 4/chunk)", async () => {
        const N = bigInt(2 ** 11 + 2);
        const a = bigInt(2 ** 11 + 1);
        const b = bigInt(2 ** 11 + 1);
        const input =
            Object.assign({},
                splitToWords(a, 4, 3, "a"),
                splitToWords(b, 4, 3, "b"),
                splitToWords(N, 4, 3, "modulus"),
            );
        const witness = bit12.calculateWitness(input);
        const output = a.times(b).mod(N);
        assertWitnessHas(bit12, witness, "prod", output, 4, 3);
    });
    it("should compute with high value quotient (12 bits, 4/chunk)", async () => {
        const N = bigInt(2 ** 11 + 1);
        const a = bigInt(2 ** 11);
        const b = bigInt(2 ** 11);
        const input =
            Object.assign({},
                splitToWords(a, 4, 3, "a"),
                splitToWords(b, 4, 3, "b"),
                splitToWords(N, 4, 3, "modulus"),
            );
        const witness = bit12.calculateWitness(input);
        const output = a.times(b).mod(N);
        assertWitnessHas(bit12, witness, "prod", output, 4, 3);
    });
});
