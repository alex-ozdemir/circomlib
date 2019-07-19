const chai = require("chai");
const path = require("path");
const snarkjs = require("snarkjs");

const compiler = require("circom");

chai.should();

describe("RabinVerifier2048", () => {
    var cirDef;

    before(async () => {
        cirDef = await compiler(path.join(__dirname, "..", "circuits", "bigint", "rabin_2048.circom"));
    });

    it("should be compilable", async () => {
        new snarkjs.Circuit(cirDef);
    });

    it("should have <= 10,652 constraints", async () => {
        // n(5w + 13) - 4
        //  = 32 * (5 * 64 + 13) - 4
        //  = 10652
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.nConstraints.should.be.at.most(10652);
    });

    it("should verify pk = ..., msg = 1:0, sig = 2**32", async () => {
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.calculateWitness({
            "msg[0]": "0",
            "msg[1]": "1",
            "msg[2]": "0",
            "msg[3]": "0",
            "msg[4]": "0",
            "msg[5]": "0",
            "msg[6]": "0",
            "msg[7]": "0",
            "msg[8]": "0",
            "msg[9]": "0",
            "msg[10]": "0",
            "msg[11]": "0",
            "msg[12]": "0",
            "msg[13]": "0",
            "msg[14]": "0",
            "msg[15]": "0",
            "msg[16]": "0",
            "msg[17]": "0",
            "msg[18]": "0",
            "msg[19]": "0",
            "msg[20]": "0",
            "msg[21]": "0",
            "msg[22]": "0",
            "msg[23]": "0",
            "msg[24]": "0",
            "msg[25]": "0",
            "msg[26]": "0",
            "msg[27]": "0",
            "msg[28]": "0",
            "msg[29]": "0",
            "msg[30]": "0",
            "msg[31]": "0",
            "sig[0]": "4294967296",
            "sig[1]": "0",
            "sig[2]": "0",
            "sig[3]": "0",
            "sig[4]": "0",
            "sig[5]": "0",
            "sig[6]": "0",
            "sig[7]": "0",
            "sig[8]": "0",
            "sig[9]": "0",
            "sig[10]": "0",
            "sig[11]": "0",
            "sig[12]": "0",
            "sig[13]": "0",
            "sig[14]": "0",
            "sig[15]": "0",
            "sig[16]": "0",
            "sig[17]": "0",
            "sig[18]": "0",
            "sig[19]": "0",
            "sig[20]": "0",
            "sig[21]": "0",
            "sig[22]": "0",
            "sig[23]": "0",
            "sig[24]": "0",
            "sig[25]": "0",
            "sig[26]": "0",
            "sig[27]": "0",
            "sig[28]": "0",
            "sig[29]": "0",
            "sig[30]": "0",
            "sig[31]": "0",
            "pk[0]": "15955770243591670207",
            "pk[1]": "17741905833247127636",
            "pk[2]": "1947486341601091155",
            "pk[3]": "14449223716353746850",
            "pk[4]": "12634908742236541043",
            "pk[5]": "8972736483110474060",
            "pk[6]": "6233251936929628619",
            "pk[7]": "8983567504864952825",
            "pk[8]": "148260967887724291",
            "pk[9]": "14322746799794142864",
            "pk[10]": "11794461584266160877",
            "pk[11]": "7741041573915547780",
            "pk[12]": "15689486254657213055",
            "pk[13]": "7138292978741378689",
            "pk[14]": "8140826210252842585",
            "pk[15]": "11132978631085486524",
            "pk[16]": "8542752691041082239",
            "pk[17]": "4054602931199839000",
            "pk[18]": "6821693799476752929",
            "pk[19]": "1052215007658208379",
            "pk[20]": "323706542501972465",
            "pk[21]": "9033323806522921803",
            "pk[22]": "5389990812728777363",
            "pk[23]": "5516139327447297714",
            "pk[24]": "5048857230303831076",
            "pk[25]": "5150553546297284307",
            "pk[26]": "4278035892115273827",
            "pk[27]": "14037820103491698809",
            "pk[28]": "6157651974283196470",
            "pk[29]": "150355884057299926",
            "pk[30]": "4618279803064218502",
            "pk[31]": "13105165289156287963",
            "x[0]": "0",
            "x[1]": "0",
            "x[2]": "0",
            "x[3]": "0",
            "x[4]": "0",
            "x[5]": "0",
            "x[6]": "0",
            "x[7]": "0",
            "x[8]": "0",
            "x[9]": "0",
            "x[10]": "0",
            "x[11]": "0",
            "x[12]": "0",
            "x[13]": "0",
            "x[14]": "0",
            "x[15]": "0",
            "x[16]": "0",
            "x[17]": "0",
            "x[18]": "0",
            "x[19]": "0",
            "x[20]": "0",
            "x[21]": "0",
            "x[22]": "0",
            "x[23]": "0",
            "x[24]": "0",
            "x[25]": "0",
            "x[26]": "0",
            "x[27]": "0",
            "x[28]": "0",
            "x[29]": "0",
            "x[30]": "0",
            "x[31]": "0",
        });
    });

    it("should verify pk = ..., msg = 225, sig = 15", async () => {
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.calculateWitness({
            "pk[0]": "15955770243591670207",
            "pk[1]": "17741905833247127636",
            "pk[2]": "1947486341601091155",
            "pk[3]": "14449223716353746850",
            "pk[4]": "12634908742236541043",
            "pk[5]": "8972736483110474060",
            "pk[6]": "6233251936929628619",
            "pk[7]": "8983567504864952825",
            "pk[8]": "148260967887724291",
            "pk[9]": "14322746799794142864",
            "pk[10]": "11794461584266160877",
            "pk[11]": "7741041573915547780",
            "pk[12]": "15689486254657213055",
            "pk[13]": "7138292978741378689",
            "pk[14]": "8140826210252842585",
            "pk[15]": "11132978631085486524",
            "pk[16]": "8542752691041082239",
            "pk[17]": "4054602931199839000",
            "pk[18]": "6821693799476752929",
            "pk[19]": "1052215007658208379",
            "pk[20]": "323706542501972465",
            "pk[21]": "9033323806522921803",
            "pk[22]": "5389990812728777363",
            "pk[23]": "5516139327447297714",
            "pk[24]": "5048857230303831076",
            "pk[25]": "5150553546297284307",
            "pk[26]": "4278035892115273827",
            "pk[27]": "14037820103491698809",
            "pk[28]": "6157651974283196470",
            "pk[29]": "150355884057299926",
            "pk[30]": "4618279803064218502",
            "pk[31]": "13105165289156287963",
            "sig[0]": "15",
            "sig[1]": "0",
            "sig[2]": "0",
            "sig[3]": "0",
            "sig[4]": "0",
            "sig[5]": "0",
            "sig[6]": "0",
            "sig[7]": "0",
            "sig[8]": "0",
            "sig[9]": "0",
            "sig[10]": "0",
            "sig[11]": "0",
            "sig[12]": "0",
            "sig[13]": "0",
            "sig[14]": "0",
            "sig[15]": "0",
            "sig[16]": "0",
            "sig[17]": "0",
            "sig[18]": "0",
            "sig[19]": "0",
            "sig[20]": "0",
            "sig[21]": "0",
            "sig[22]": "0",
            "sig[23]": "0",
            "sig[24]": "0",
            "sig[25]": "0",
            "sig[26]": "0",
            "sig[27]": "0",
            "sig[28]": "0",
            "sig[29]": "0",
            "sig[30]": "0",
            "sig[31]": "0",
            "msg[0]": "225",
            "msg[1]": "0",
            "msg[2]": "0",
            "msg[3]": "0",
            "msg[4]": "0",
            "msg[5]": "0",
            "msg[6]": "0",
            "msg[7]": "0",
            "msg[8]": "0",
            "msg[9]": "0",
            "msg[10]": "0",
            "msg[11]": "0",
            "msg[12]": "0",
            "msg[13]": "0",
            "msg[14]": "0",
            "msg[15]": "0",
            "msg[16]": "0",
            "msg[17]": "0",
            "msg[18]": "0",
            "msg[19]": "0",
            "msg[20]": "0",
            "msg[21]": "0",
            "msg[22]": "0",
            "msg[23]": "0",
            "msg[24]": "0",
            "msg[25]": "0",
            "msg[26]": "0",
            "msg[27]": "0",
            "msg[28]": "0",
            "msg[29]": "0",
            "msg[30]": "0",
            "msg[31]": "0",
            "x[0]": "0",
            "x[1]": "0",
            "x[2]": "0",
            "x[3]": "0",
            "x[4]": "0",
            "x[5]": "0",
            "x[6]": "0",
            "x[7]": "0",
            "x[8]": "0",
            "x[9]": "0",
            "x[10]": "0",
            "x[11]": "0",
            "x[12]": "0",
            "x[13]": "0",
            "x[14]": "0",
            "x[15]": "0",
            "x[16]": "0",
            "x[17]": "0",
            "x[18]": "0",
            "x[19]": "0",
            "x[20]": "0",
            "x[21]": "0",
            "x[22]": "0",
            "x[23]": "0",
            "x[24]": "0",
            "x[25]": "0",
            "x[26]": "0",
            "x[27]": "0",
            "x[28]": "0",
            "x[29]": "0",
            "x[30]": "0",
            "x[31]": "0",
        });
    });

    it("should verify pk = ..., msg, sig = pows of 10", async () => {
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.calculateWitness({
            "msg[0]": "0",
            "msg[1]": "13259384185010782208",
            "msg[2]": "10903954450442161157",
            "msg[3]": "4682955357782187069",
            "msg[4]": "86361685550944446",
            "msg[5]": "0",
            "msg[6]": "0",
            "msg[7]": "0",
            "msg[8]": "0",
            "msg[9]": "0",
            "msg[10]": "0",
            "msg[11]": "0",
            "msg[12]": "0",
            "msg[13]": "0",
            "msg[14]": "0",
            "msg[15]": "0",
            "msg[16]": "0",
            "msg[17]": "0",
            "msg[18]": "0",
            "msg[19]": "0",
            "msg[20]": "0",
            "msg[21]": "0",
            "msg[22]": "0",
            "msg[23]": "0",
            "msg[24]": "0",
            "msg[25]": "0",
            "msg[26]": "0",
            "msg[27]": "0",
            "msg[28]": "0",
            "msg[29]": "0",
            "msg[30]": "0",
            "msg[31]": "0",
            "sig[0]": "6450984253743169536",
            "sig[1]": "13015503840481697412",
            "sig[2]": "293873587",
            "sig[3]": "0",
            "sig[4]": "0",
            "sig[5]": "0",
            "sig[6]": "0",
            "sig[7]": "0",
            "sig[8]": "0",
            "sig[9]": "0",
            "sig[10]": "0",
            "sig[11]": "0",
            "sig[12]": "0",
            "sig[13]": "0",
            "sig[14]": "0",
            "sig[15]": "0",
            "sig[16]": "0",
            "sig[17]": "0",
            "sig[18]": "0",
            "sig[19]": "0",
            "sig[20]": "0",
            "sig[21]": "0",
            "sig[22]": "0",
            "sig[23]": "0",
            "sig[24]": "0",
            "sig[25]": "0",
            "sig[26]": "0",
            "sig[27]": "0",
            "sig[28]": "0",
            "sig[29]": "0",
            "sig[30]": "0",
            "sig[31]": "0",
            "pk[0]": "15955770243591670207",
            "pk[1]": "17741905833247127636",
            "pk[2]": "1947486341601091155",
            "pk[3]": "14449223716353746850",
            "pk[4]": "12634908742236541043",
            "pk[5]": "8972736483110474060",
            "pk[6]": "6233251936929628619",
            "pk[7]": "8983567504864952825",
            "pk[8]": "148260967887724291",
            "pk[9]": "14322746799794142864",
            "pk[10]": "11794461584266160877",
            "pk[11]": "7741041573915547780",
            "pk[12]": "15689486254657213055",
            "pk[13]": "7138292978741378689",
            "pk[14]": "8140826210252842585",
            "pk[15]": "11132978631085486524",
            "pk[16]": "8542752691041082239",
            "pk[17]": "4054602931199839000",
            "pk[18]": "6821693799476752929",
            "pk[19]": "1052215007658208379",
            "pk[20]": "323706542501972465",
            "pk[21]": "9033323806522921803",
            "pk[22]": "5389990812728777363",
            "pk[23]": "5516139327447297714",
            "pk[24]": "5048857230303831076",
            "pk[25]": "5150553546297284307",
            "pk[26]": "4278035892115273827",
            "pk[27]": "14037820103491698809",
            "pk[28]": "6157651974283196470",
            "pk[29]": "150355884057299926",
            "pk[30]": "4618279803064218502",
            "pk[31]": "13105165289156287963",
            "x[0]": "0",
            "x[1]": "0",
            "x[2]": "0",
            "x[3]": "0",
            "x[4]": "0",
            "x[5]": "0",
            "x[6]": "0",
            "x[7]": "0",
            "x[8]": "0",
            "x[9]": "0",
            "x[10]": "0",
            "x[11]": "0",
            "x[12]": "0",
            "x[13]": "0",
            "x[14]": "0",
            "x[15]": "0",
            "x[16]": "0",
            "x[17]": "0",
            "x[18]": "0",
            "x[19]": "0",
            "x[20]": "0",
            "x[21]": "0",
            "x[22]": "0",
            "x[23]": "0",
            "x[24]": "0",
            "x[25]": "0",
            "x[26]": "0",
            "x[27]": "0",
            "x[28]": "0",
            "x[29]": "0",
            "x[30]": "0",
            "x[31]": "0",
        });
    });

    it("should verify pk = ..., msg = sig^2, sig = 1000b prime", async () => {
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.calculateWitness({
            "msg[0]": "2737380498991039273",
            "msg[1]": "9922624229045128230",
            "msg[2]": "10001960719936991664",
            "msg[3]": "3707253568935035382",
            "msg[4]": "7871591691354222216",
            "msg[5]": "16647015651164829255",
            "msg[6]": "3779936578504893635",
            "msg[7]": "9447425406318584640",
            "msg[8]": "1636194044544997538",
            "msg[9]": "2386803027465347296",
            "msg[10]": "16423796683650650292",
            "msg[11]": "11002004474176419901",
            "msg[12]": "8454967386813088327",
            "msg[13]": "11606980546790734999",
            "msg[14]": "15289177297844572644",
            "msg[15]": "14700433131211646983",
            "msg[16]": "2497982125163956545",
            "msg[17]": "8808022165775828026",
            "msg[18]": "14681275255596017255",
            "msg[19]": "1279553647271770562",
            "msg[20]": "15479341004716383208",
            "msg[21]": "6546638107279286328",
            "msg[22]": "11755180197171729462",
            "msg[23]": "17444832612508709466",
            "msg[24]": "13000682264468489271",
            "msg[25]": "142154012713201246",
            "msg[26]": "7912107191772997676",
            "msg[27]": "11830446299829449254",
            "msg[28]": "13124391985612838445",
            "msg[29]": "13011927207180567100",
            "msg[30]": "9956972120730271689",
            "msg[31]": "45583",
            "sig[0]": "4819187580044832333",
            "sig[1]": "9183764011217009606",
            "sig[2]": "11426964127496009747",
            "sig[3]": "17898263845095661790",
            "sig[4]": "12102522037140783322",
            "sig[5]": "4029304176671511763",
            "sig[6]": "11339410859987005436",
            "sig[7]": "12120243430436644729",
            "sig[8]": "2888435820322958146",
            "sig[9]": "7612614626488966390",
            "sig[10]": "3872170484348249672",
            "sig[11]": "9589147526444685354",
            "sig[12]": "16391157694429928307",
            "sig[13]": "12256166884204507566",
            "sig[14]": "4257963982333550934",
            "sig[15]": "916988490704",
            "sig[16]": "0",
            "sig[17]": "0",
            "sig[18]": "0",
            "sig[19]": "0",
            "sig[20]": "0",
            "sig[21]": "0",
            "sig[22]": "0",
            "sig[23]": "0",
            "sig[24]": "0",
            "sig[25]": "0",
            "sig[26]": "0",
            "sig[27]": "0",
            "sig[28]": "0",
            "sig[29]": "0",
            "sig[30]": "0",
            "sig[31]": "0",
            "pk[0]": "15955770243591670207",
            "pk[1]": "17741905833247127636",
            "pk[2]": "1947486341601091155",
            "pk[3]": "14449223716353746850",
            "pk[4]": "12634908742236541043",
            "pk[5]": "8972736483110474060",
            "pk[6]": "6233251936929628619",
            "pk[7]": "8983567504864952825",
            "pk[8]": "148260967887724291",
            "pk[9]": "14322746799794142864",
            "pk[10]": "11794461584266160877",
            "pk[11]": "7741041573915547780",
            "pk[12]": "15689486254657213055",
            "pk[13]": "7138292978741378689",
            "pk[14]": "8140826210252842585",
            "pk[15]": "11132978631085486524",
            "pk[16]": "8542752691041082239",
            "pk[17]": "4054602931199839000",
            "pk[18]": "6821693799476752929",
            "pk[19]": "1052215007658208379",
            "pk[20]": "323706542501972465",
            "pk[21]": "9033323806522921803",
            "pk[22]": "5389990812728777363",
            "pk[23]": "5516139327447297714",
            "pk[24]": "5048857230303831076",
            "pk[25]": "5150553546297284307",
            "pk[26]": "4278035892115273827",
            "pk[27]": "14037820103491698809",
            "pk[28]": "6157651974283196470",
            "pk[29]": "150355884057299926",
            "pk[30]": "4618279803064218502",
            "pk[31]": "13105165289156287963",
            "x[0]": "0",
            "x[1]": "0",
            "x[2]": "0",
            "x[3]": "0",
            "x[4]": "0",
            "x[5]": "0",
            "x[6]": "0",
            "x[7]": "0",
            "x[8]": "0",
            "x[9]": "0",
            "x[10]": "0",
            "x[11]": "0",
            "x[12]": "0",
            "x[13]": "0",
            "x[14]": "0",
            "x[15]": "0",
            "x[16]": "0",
            "x[17]": "0",
            "x[18]": "0",
            "x[19]": "0",
            "x[20]": "0",
            "x[21]": "0",
            "x[22]": "0",
            "x[23]": "0",
            "x[24]": "0",
            "x[25]": "0",
            "x[26]": "0",
            "x[27]": "0",
            "x[28]": "0",
            "x[29]": "0",
            "x[30]": "0",
            "x[31]": "0"
        });
    });

    it("should verify pk = ..., msg = sig^2, sig = 2000b prime", async () => {
        const circuit = new snarkjs.Circuit(cirDef);
        circuit.calculateWitness({
            "msg[0]": "12381826773980082464",
            "msg[1]": "17736470229918674891",
            "msg[2]": "7286855239737640606",
            "msg[3]": "1286434590086188248",
            "msg[4]": "11573481493214879822",
            "msg[5]": "7909054266695096585",
            "msg[6]": "4244624920316139915",
            "msg[7]": "1469488031552764435",
            "msg[8]": "13633212958258362953",
            "msg[9]": "5058620059202496395",
            "msg[10]": "17089171913668700813",
            "msg[11]": "12260117275449872042",
            "msg[12]": "5800739751096346995",
            "msg[13]": "863630603281039415",
            "msg[14]": "11762890178909666778",
            "msg[15]": "17910489422468044763",
            "msg[16]": "17237326335272468471",
            "msg[17]": "2293828049819281155",
            "msg[18]": "9517038377543775789",
            "msg[19]": "3010596816041971943",
            "msg[20]": "15596658608787602992",
            "msg[21]": "7198887618656527039",
            "msg[22]": "2826111195827256463",
            "msg[23]": "8501261302155317807",
            "msg[24]": "8747679053575689469",
            "msg[25]": "11090689564027192694",
            "msg[26]": "16869597705046320772",
            "msg[27]": "16364783300622848692",
            "msg[28]": "1650345223871658168",
            "msg[29]": "10174634799051795879",
            "msg[30]": "10838511392191365499",
            "msg[31]": "1065981206786797439",
            "sig[0]": "18183355809974526279",
            "sig[1]": "703863700685793898",
            "sig[2]": "4636523964402022052",
            "sig[3]": "11982045082130259594",
            "sig[4]": "14665118758514082261",
            "sig[5]": "1977242634604866925",
            "sig[6]": "1187044739514790141",
            "sig[7]": "18129219232727421604",
            "sig[8]": "5544518633634950599",
            "sig[9]": "15404311702494068980",
            "sig[10]": "16187005796130865052",
            "sig[11]": "8243540120106559053",
            "sig[12]": "14844190357595342205",
            "sig[13]": "4259501431739928171",
            "sig[14]": "12981711474483613033",
            "sig[15]": "6854237528453402449",
            "sig[16]": "9143402880469690768",
            "sig[17]": "2505659671942280749",
            "sig[18]": "323689252274004460",
            "sig[19]": "11689948420716121416",
            "sig[20]": "12154824643066749363",
            "sig[21]": "14783926030561953455",
            "sig[22]": "10731417423845472162",
            "sig[23]": "10428427181600954129",
            "sig[24]": "17008612230362548881",
            "sig[25]": "18176237347585963517",
            "sig[26]": "4186746606669795732",
            "sig[27]": "9631626448458404686",
            "sig[28]": "10208319195838626158",
            "sig[29]": "17682508230060818552",
            "sig[30]": "6533997406843078602",
            "sig[31]": "62463",
            "pk[0]": "15955770243591670207",
            "pk[1]": "17741905833247127636",
            "pk[2]": "1947486341601091155",
            "pk[3]": "14449223716353746850",
            "pk[4]": "12634908742236541043",
            "pk[5]": "8972736483110474060",
            "pk[6]": "6233251936929628619",
            "pk[7]": "8983567504864952825",
            "pk[8]": "148260967887724291",
            "pk[9]": "14322746799794142864",
            "pk[10]": "11794461584266160877",
            "pk[11]": "7741041573915547780",
            "pk[12]": "15689486254657213055",
            "pk[13]": "7138292978741378689",
            "pk[14]": "8140826210252842585",
            "pk[15]": "11132978631085486524",
            "pk[16]": "8542752691041082239",
            "pk[17]": "4054602931199839000",
            "pk[18]": "6821693799476752929",
            "pk[19]": "1052215007658208379",
            "pk[20]": "323706542501972465",
            "pk[21]": "9033323806522921803",
            "pk[22]": "5389990812728777363",
            "pk[23]": "5516139327447297714",
            "pk[24]": "5048857230303831076",
            "pk[25]": "5150553546297284307",
            "pk[26]": "4278035892115273827",
            "pk[27]": "14037820103491698809",
            "pk[28]": "6157651974283196470",
            "pk[29]": "150355884057299926",
            "pk[30]": "4618279803064218502",
            "pk[31]": "13105165289156287963",
            "x[0]": "14871092535685708207",
            "x[1]": "8174344943349649908",
            "x[2]": "15075554186924885086",
            "x[3]": "1051148353762676918",
            "x[4]": "12610910193777966173",
            "x[5]": "12714737364847567524",
            "x[6]": "5800450962833489699",
            "x[7]": "6201768781401529045",
            "x[8]": "13853075266636479546",
            "x[9]": "10943981128309841653",
            "x[10]": "8207202893533626950",
            "x[11]": "12007464947058395443",
            "x[12]": "12480274979063669326",
            "x[13]": "15445478434811594407",
            "x[14]": "13050790624846394096",
            "x[15]": "13725529165070485169",
            "x[16]": "14425827852659449086",
            "x[17]": "15855476496410126472",
            "x[18]": "2886960717710626015",
            "x[19]": "17584467981535765679",
            "x[20]": "4815615475291517985",
            "x[21]": "7320581048868527331",
            "x[22]": "4570614358104477293",
            "x[23]": "13269524084226536366",
            "x[24]": "17581091769222249149",
            "x[25]": "17217862957817626285",
            "x[26]": "16643343218461599591",
            "x[27]": "9768163664507818654",
            "x[28]": "3919633239520423609",
            "x[29]": "9773360905605459521",
            "x[30]": "5491965784",
            "x[31]": "0",
        });
    });
});
