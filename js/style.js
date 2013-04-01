// Various functions relative to the styling of the page.

var shadowHeight = 6;
var effects = [colorsTrans, colorsRun, colorsBlink, shadowColor];

$(document).ready(function() {
    getEffect()($("#logo"));
});

function getEffect() {
    return effects[Math.floor(Math.random() * effects.length)];
}

function colorsTrans(el) {
    el.css("transition", "color 1s");

    var changeColor = function () { el.css("color", nextColor()); };
    transitionEnd(el, changeColor);

    changeColor();
}

// TODO is it worth doing that with transitions?
function colorsRun(el) {
    var colors = [];
    var spans = spannify(el);
    var i;

    for (i = 0; i < spans.length; i++) {
        colors[i] = nextColor(200);
    }

    var changeColors = function() {
        var i;
        for (i = 0; i < spans.length; i++) {
            spans[i].css("color", colors[i]);
        }

        colors.shift();
        colors.push(nextColor(200));

        setTimeout(changeColors, 100);
    };

    changeColors();
}

function colorsBlink(el) {
    el.css("transition", "color 0.3s");

    var toNext = function() {
        transitionEnd(el, toBack);
        el.css("color", nextColor());
    };
    var toBack = function() {
        transitionEnd(el, toNext);
        setTimeout(function() {
            el.css("color", $(document.body).css("background-color"));
        }, 500);
    };

    toBack();
}

function shadowColor(el) {
    el.css("transition", "text-shadow 0.1s");
    var colors = [];
    var i;

    for (i = 0; i < shadowHeight; i++) {
        colors[i] = nextColor();
    }

    var colorShadow = function() {
        colors.shift();
        colors.push(nextColor());

        el.css("text-shadow", buildShadow(colors));
    };

    transitionEnd(el, colorShadow);

    colorShadow();
}

// TODO fixme
function shadowHeights(el) {
    var jump = 2;
    var i;

    var shadow = function(height) {
        var i;
        colors = [];
        for (i = 0; i < height; i++) {
            colors.push("#476871");
        }
        return buildShadow(colors);
    }

    var change = function(el, h) {
        var newh;
        if (h < shadowHeight / 2) {
            newh = h + jump + random(shadowHeight - h - jump);
        } else {
            newh = h - jump - random(h - jump);
        }
        console.log(newh);
        transitionEnd(el, function() { change(el, newh); });
        el.css("text-shadow", shadow(newh));
    }

    var spans = spannify(el);
    for (i = 0; i < 1; i++) {
        spans[i].css("transition", "text-shadow 1s");
        change(spans[i], shadowHeight);
    }
}

function spannify(el) {
    var spans = [];
    var i;
    var s = el.text();

    for (i = 0; i < s.length; i++) {
        spans[i] = $("<span>", {text: s.charAt(i)});
    }

    el.empty();

    for (i = 0; i < spans.length; i++) {
        spans[i].appendTo(el);
    }

    return spans;
}

function nextColor(treshold_up, treshold_down) {
    if (treshold_up === undefined) {
        treshold_up = 256;
    }
    if (treshold_down === undefined) {
        treshold_down = 0;
    }

    var r = random(256);
    var g = random(256);
    var b = random(256);

    if (r + g + b > treshold_up || r + g + b < treshold_down) {
        return nextColor(treshold_up, treshold_down);
    }

    return "rgb(" + r + "," + g + "," + b + ")";
}

function random(i) {
    return Math.floor(Math.random() * i);
}

function transitionEnd(el, f) {
    el.unbind("transitionend webkitTransitionEnd oTransitionEnd MSTransitionEnd");
    el.bind("transitionend webkitTransitionEnd oTransitionEnd MSTransitionEnd", f);
}

function buildShadow(colors) {
    var shadow = "1px 1px 0px black";

    for (i = 0; i < colors.length; i++) {
        shadow += ', ' + (i + 2) + 'px ' + (i + 2) + 'px ' + '0px ' + colors[i];
    }

    return shadow;
}