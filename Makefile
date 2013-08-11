
all: site cv/cv.html cv/cv.pdf cv/cv.txt
	./site build

site: site.hs
	ghc --make site.hs

cv/cv.html: cv.html $(HTML_FILES)
	sed 's/%%font-size%%/1em/' cv.html |  sed 's/%%formats%%/<li class="formats"><a href=".\/cv.txt">plain text<\/a> \&middot; <a href=".\/cv.pdf">pdf<\/a><\/li>/' > $@

cv/cv-nofmts.html: cv.html $(HTML_FILES)
	sed 's/%%font-size%%/11pt/' cv.html | sed 's/%%formats%%//' > $@

cv/cv.txt: cv/cv-nofmts.html plaintext
	./plaintext < cv/cv-nofmts.html | sed 's/-   <f@mazzo.li>/<f@mazzo.li>/' > $@

cv/cv.pdf: cv/cv-nofmts.html
	wkhtmltopdf -B 20 -L 25 -T 20 -R 25 cv/cv-nofmts.html cv/cv.pdf

plaintext:
	ghc --make plaintext.hs

clean: site
	./site clean
	find . -name "*.o" | xargs rm -f
	find . -name "*.hi" | xargs rm -f
	find . -name "*.agdai" | xargs rm -f
	rm -f site cv/cv.html cv/cv-nofmts.html cv/cv.txt cv/cv.pdf plaintext
