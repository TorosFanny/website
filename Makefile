SITE = ./dist/build/site/site
PLAINTEXT = ./dist/build/plaintext/plaintext

all: $(SITE) cv/cv.html
	$(SITE) build

$(SITE): site.hs
	cabal build

cv/cv.html: cv.html
	cp cv.html cv/cv.html

agdalib:
	wget https://github.com/agda/agda-stdlib/archive/v0.8.1.tar.gz
	tar xzvf v0.8.1.tar.gz
	rm -f v0.8.1.tar.gz
	mv agda-stdlib-0.8.1 agdalib

$(PLAINTEXT): plaintext.hs
	cabal build

clean:
	$(SITE) clean
	cabal clean
	rm -f site cv/cv.html
