module Messages(initMsg,msgR,msgW,msgs) where

initMsg="ねえ 起きてよ・・・。 {ch.起きる,s0.起きない,initMsg}"

s0="\n{sm}\n古い順に並べて {rk.1.z.abc.sc0}"

sc0="\nせいかい！。"

msgR="\nまう一度 やってみませう"

msgW="\n何が起：お：こった？"

nubatama="\nぬばたまの 世は難しく 思へれど。   \n明けて見ゆるは 唯大河なり"

s1="\nものを かぞへるのが 數：かず：です。\nもし 私たちが この世界を 分：わ：けて考：かんが：へないなら 數は必：ひつ：要：やう：ありません。\n分けられてゐるから 數へることができます {da}{e.b0.m0:s100}"

s100="\nこれは 分けられますか？ {ch.はい,s1_0.いいえ,s1_1}"

s1_0="\nでは 分けてください {ct.0.Fr}{d.b0}{e.e0.m0:s101}"

s1_1="\n本：ほん：當：たう：に分けられないのでせうか"

s101="\nあなたが これを取：と：ったので それは まうここにありません。\nこれは 分けたことになりますか？ {ch.はい,s1_2.いいえ,s1_3}"

s1_2="\nあなたは 世界を 分けて\n「在：あ：る。\n「無：な：い。\nをつくりました。\nそれでは この ＜在る＞を 1 と呼：よ：びませう {d.e0}{p.0,4.1,Fr}{e.e1.m1:s102}"

s1_3="\nあなたが 分けたと思：おも：はないのであれば。\nそれは 分かれてゐません"

s102="\n＜在る＞といふ存在と ＜無い＞といふ存在ができました。\n＜存在＞を 1 とするなら これらを合はせた名前をつくりませう {d.e1}{p.4,4.2,Fr}{e.o2.m0:s103}"

s103="\n＜在る＞が存在する限：かぎ：り 數は無：む：限：げん：につくることができます。\nこれらが最：さい：初：しょ：に置：お：かれてゐた位：い：置：ち：を入：い：れ替：か：へたら 何：なに：か起：お：こりさうです {m.isp.0_Fr_getpos_(0,4)_==_2_Fr_getpos_(2,0)_==_&&_1_Fr_getpos_(4,4)_==_&&}{if.isp.T.p.2,2.3,Fr}{if.isp.T.d.o2}{if.isp.T.e.e3.m1:s104}"

s104="\n火：ひ：(１)と水：みづ：(２)を合はせると ひみつ(３) になります。\n秘：ひ：密：みつ：の扉：とびら：は まう開：ひら：かれるでせう。\n鍵：かぎ：を手に入れたのですから {e.==.m1:s1c}{p.1,1.+,Bl}{p.3,1.=,Bl}{d.e3 }"

s1c="\n扉が開かれたやうです {ct.0.Ex}{e.c1&s4.m1:s4}{e.u0.jl4}"

s2="\nものごとの筋：すじ：道：みち：が 理：ことはり：です。\n本：ほん：當：たう：のこと 嘘：うそ：のこと。\n正：ただ：しいこと 間：ま：違：ちが：ってゐること。\nそれを はっきりさせるのが 理 です"

s3="\nこの世界に遺：のこ：された言：こと：葉：ば： それが 史：ふみ： です。\n私たちは それによって 人：じん：生：せい：の長さをはるかに越：こ：えた 記：き：憶：おく：を辿：たど：ることができます。"

s4="\n4つの數で 東：き：西：つ： 南：さ：北：ね：の 4方向が數へられます。\nそれに 中：ちゅう：心：しん：を加：くは：へると 5つになります。\n5 は あいうえお。\n私：わたし：達：たち：の國：くに：に住：す：む人：ひと：々：びと：の 母：はは：なる音：おと：です"


msgs=[("initMsg",initMsg),("s0",s0),("sc0",sc0),("msgR",msgR),("msgW",msgW),("nubatama",nubatama),("s1",s1),("s100",s100),("s1_0",s1_0),("s1_1",s1_1),("s101",s101),("s1_2",s1_2),("s1_3",s1_3),("s102",s102),("s103",s103),("s104",s104),("s1c",s1c),("s2",s2),("s3",s3),("s4",s4)]