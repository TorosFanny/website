
all: site cv/cv.html cv/cv.txt
	./dist/build/site/site build

site: site.hs
	cabal build

cv/cv.html: cv.html $(HTML_FILES)
	sed 's/%%font-size%%/1em/' cv.html |  sed 's/%%formats%%/<li class="formats"><a href=".\/cv.txt">plain text<\/a><\/li>/' > $@

cv/cv-nofmts.html: cv.html $(HTML_FILES)
	sed 's/%%font-size%%/11pt/' cv.html | sed 's/%%formats%%//' > $@

cv/cv.txt: cv/cv-nofmts.html plaintext
	./plaintext < cv/cv-nofmts.html | sed 's/-   <f@mazzo.li>/<f@mazzo.li>/' > $@

cv/cv.pdf: cv/cv-nofmts.html
	wkhtmltopdf -B 20 -L 25 -T 20 -R 25 cv/cv-nofmts.html cv/cv.pdf

agdalib:
	wget http://www.cse.chalmers.se/~nad/software/lib-0.7.tar.gz
	tar xzvf lib-0.7.tar.gz
	rm -f lib-0.7.tar.gz
	mv lib-0.7 agdalib

plaintext:
	ghc --make plaintext.hs

clean: site
	./dist/build/site/site clean
	cabal clean
	rm -f site cv/cv.html cv/cv-nofmts.html cv/cv.txt cv/cv.pdf plaintext
