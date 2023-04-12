app := $(wildcard */App.fst)

all: app.fsti framework app.fst clean

app.fsti: SeqUtils.fst
	fstar.exe App.fsti
 
framework: App.fsti SeqUtils.fst
	fstar.exe Framework.fst

app.fst: App.fsti Framework.fst SeqUtils.fst
	fstar.exe $(app)

clean:
	rm -f *~	
