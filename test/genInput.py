def _wordify(x, w, n):
    return [] if n == 0 else [x % (2 ** w)] + _wordify(x >> w, w, n - 1)

def _dewordify(X, w):
    return 0 if len(X) == 0 else (_dewordify(X[1:], w) << w) + X[0]

def wordify(x):
    return _wordify(x, 64, 32)

def dewordify(x):
    return _dewordify(x, 64)


p = 141484354634323830210079605471461836165894419289183522840657958191854239720288111994726808441316783312221535936863180754384061438556824658567734700364687023352338914708665533363154299889383212023948533288349834048937719667272806922970885809280881362263758435001412593248260338720155330385899996833029316928303
q = 162272707380164238452768663141550179314344728778717312236305573415604755990347278091416409317064961015950841314838846635517821502761887081685954648600006517065440921264058316650144563943015956712719799232896235901014161632006492450066777898434668423992002273288779535236411431665359686441728352764455807049329
N = p * q

def gcd(x, y):
    if x > y:
        return gcd(y, x)
    elif x == 0:
        return y
    else:
        return gcd(y % x, x)

def bezout(x, y):
    ''' Given x, y return (a, b) s.t. ax + by = gcd(x, y) '''
    if x < y:
        return bezout(y, x)[::-1]
    elif y == 0:
        return (1, 1)
    else:
        r = x  % y
        q = x // y
        cy, cr = bezout(y, r)
        return (cr, cy - cr * q)

def fastexp(b, e, m):
    if e == 0:
        return b % m
    elif (e & 1) == 1:
        return fastexp(b * b % m, e >> 1, m) * b % m
    else:
        return fastexp(b * b % m, e >> 1, m)

def inbase(n, b):
    return '' if n == 0 else inbase(n // b, b) + str(n % b)

def emit(x, name):
    words = wordify(x)
    assert dewordify(words) == x
    for i, x in enumerate(words):
        print(f'            "{name}[{i}]": "{x}",')


phi = (p - 1) * (q - 1)
ek = 3
dk = bezout(ek, phi)[0] % phi
assert ek * dk % phi == 1
sig = 109430075526134183403196070680189002006275007424892395439977036959072964575101098869038336207527435358436629638972217268719959001742323625277512150707272326612794095812703785226776247555343720567519022299132200199837082228895971931483033269269567874492537901900596417957956431022704521118921621607506915363918821642029361402594473320474194874174297460584835588376592742250977487613605580382879002761732003391861756958978035618056560055669771323555863483299828042941100813372017431384050639805660868093991616650077198000116125510570930967200426266564299855172106081545366134951057827531208099370787479879
msg = sig * sig % N
x = (sig * sig - msg) // N
assert (dewordify(wordify(msg)) - dewordify(wordify(sig)) * dewordify(wordify(sig))) % N == 0
print('{')
emit(msg, "msg")
emit(sig, "sig")
emit(N, "pk")
emit(x, "x")
print('}')
