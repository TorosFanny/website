HTML_FILES = logo.png

all: cv.html cv.pdf cv.txt

cv.html: source.html $(HTML_FILES)
	sed 's/%%formats%%/<li class="formats"><a href=".\/cv.txt">Plain text<\/a> \&middot; <a href=".\/cv.pdf">Pdf<\/a><\/li>/' source.html > $@

cv-nofmts.html: source.html $(HTML_FILES)
	sed 's/%%formats%%//' source.html > $@

cv.txt: cv-nofmts.html plaintext.hs
	runhaskell plaintext.hs < cv-nofmts.html > $@

cv.pdf: cv-nofmts.html
	wkhtmltopdf cv-nofmts.html cv.pdf

clean:
	rm -f cv.html cv-nofmts.html cv.txt cv.pdf
