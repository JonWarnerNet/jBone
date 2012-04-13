// Copyright © 2012 by Jon Warner (www.jonwarner.net)
// Licensed under the LGPL license: http://www.opensource.org/licenses/lgpl-3.0.html

(function(window, undefined) {

    var DEG_TO_RAD = (Math.PI / 180);
    var RAD_TO_DEG = (180 / Math.PI);

    var document = window.document;
    var div = document.createElement('div');

    var cssTransformAttr = (div.style.transform !== undefined ? 'transform' :
                            div.style.MozTransform !== undefined ? '-moz-transform' :
                            div.style.WebkitTransform !== undefined ? '-webkit-transform' :
                            div.style.msTransform !== undefined ? '-ms-transform' :
                            div.style.OTransform !== undefined ? '-o-transform' : '');

    var cssTransformStr = (div.style.transform !== undefined ? 'transform' :
                           div.style.MozTransform !== undefined ? 'MozTransform' :
                           div.style.WebkitTransform !== undefined ? 'WebkitTransform' :
                           div.style.msTransform !== undefined ? 'msTransform' :
                           div.style.OTransform !== undefined ? 'OTransform' : '');
    var cssTransformOriginStr = (div.style.transformOrigin !== undefined ? 'transformOrigin' :
                                 div.style.MozTransformOrigin !== undefined ? 'MozTransformOrigin' :
                                 div.style.WebkitTransformOrigin !== undefined ? 'WebkitTransformOrigin' :
                                 div.style.msTransformOrigin !== undefined ? 'msTransformOrigin' :
                                 div.style.OTransformOrigin !== undefined ? 'OTransformOrigin' : '');

    function each(obj, iteratorCallback) {
        if (obj && (obj instanceof Array || obj.length)) {
            var result = null;
            for (var index = 0, length = obj.length; index < length; ++index) {
                result = iteratorCallback(obj[index]);
                if (result != null) {
                    return result;
                }
            }
        }
        return null;
    }

    function applyDefaults(options, defaultParams) {
        for (var key in defaultParams) {
            if (options[key] == undefined) {
                options[key] = defaultParams[key];
            }
        }
    }

    function elementPosition(element) {
        var left = 0;
        var top = 0;

        var width = element.offsetWidth;
        var height = element.offsetHeight;

        do {
            var localLeft = element.offsetLeft;
            var localTop = element.offsetTop;

            left += localLeft;
            top += localTop;
        } while (element = element.offsetParent);

        var right = left + width;
        var bottom = top + height;

        return new function() {
            this.left = left;
            this.top = top;
            this.right = right;
            this.bottom = bottom;
            this.width = width;
            this.height = height;
        };
    }

    var Interpolation = function() {
        var currentMethod = function(t, a, b) {
            // default is linear interpolation
            return (a + ((b - a) * t));
        };

        var customMethods = [];

        function getMethodForName(name) {
            if (customMethods[name] != undefined) {
                return customMethods[name];
            } else {
                return currentMethod;
            }
        };

        return {
            SetInterpolationMethod: function(name, method) {
                if (!(name instanceof String)) {
                    method = name;
                    currentMethod = method;
                } else {
                    customMethods[name] = method;
                }
            },
            Method: function(name, t, a, b) {
                var interpolationMethod = getMethodForName(name);
                if (a instanceof Point && b instanceof Point) {
                    // point to point returns point
                    return new Point(interpolationMethod(t, a.x, b.x), interpolationMethod(t, a.y, b.y));
                } else if (a instanceof Point && !isNaN(b)) {
                    // point to scalar returns point
                    return new Point(interpolationMethod(t, a.x, b), interpolationMethod(t, a.y, b));
                } else if (!isNaN(a) && b instanceof Point) {
                    // flip a and b do, point to scalar returns point
                    return new Point(interpolationMethod(t, b.x, a), interpolationMethod(t, b.y, a));
                } else {
                    return interpolationMethod(t, a, b);
                }
            }
        };
    } ();


    var MatrixPool = function() {
        var _matrixPool = [];
        var _currentIndex = 0;
        var _markIndex = -1;
        var _matrixPoolLimit = 0;

        return {
            Get: function() {
                if (_currentIndex >= _matrixPoolLimit || _matrixPoolLimit == 0) {
                    // increase pool limit
                    _matrixPoolLimit += 1000;

                    for (var i = _currentIndex; i < _matrixPoolLimit; i++) {
                        _matrixPool[_matrixPool.length] = new Matrix();
                    }
                }

                var matrix = _matrixPool[_currentIndex];
                matrix.matrixPoolIndex = _currentIndex;

                do {
                    _currentIndex++;
                } while (_currentIndex < _matrixPoolLimit && _matrixPool[_currentIndex].matrixPoolIndex != -1);

                if (_currentIndex >= _matrixPoolLimit) {
                    // increase pool limit
                    _matrixPoolLimit += 1000;

                    for (var i = _currentIndex; i < _matrixPoolLimit; i++) {
                        _matrixPool[_matrixPool.length] = new Matrix();
                    }
                }

                return matrix;
            },
            Release: function(matrix) {
                if (matrix == undefined) {
                    if (_markIndex >= 0) {
                        // release matrices from _currentIndex to _markIndex
                        for (var index = _markIndex; index < _currentIndex; index++) {
                            delete _matrixPool[index];
                            _matrixPool[index] = new Matrix();
                        }

                        _currentIndex = _markIndex;
                        _markIndex = -1;
                    }
                } else {
                    if (matrix.matrixPoolIndex != -1 && _matrixPool[matrix.matrixPoolIndex].matrixPoolIndex == matrix.matrixPoolIndex) {
                        var index = matrix.matrixPoolIndex;

                        delete _matrixPool[index];
                        _matrixPool[index] = new Matrix();

                        _currentIndex = index;
                    }
                }
            },
            Mark: function() {
                _markIndex = _currentIndex;
            }
        };
    } ();

    var Matrix = function() {
        this.m = [[1, 0, 0],
                  [0, 1, 0],
                  [0, 0, 1]];

        this.matrixPoolIndex = -1;

        this.identityMatrix = [[1, 0, 0],
                               [0, 1, 0],
                               [0, 0, 1]];

        this.identity = function() {
            this.m = [[1, 0, 0],
                      [0, 1, 0],
                      [0, 0, 1]];
            return this;
        };

        this.inverse = function() {
            var c01 = (this.m[2][2] * this.m[1][1]) - (this.m[1][2] * this.m[2][1]);
            var c11 = (-this.m[2][2] * this.m[1][0]) + (this.m[1][2] * this.m[2][0]);
            var c21 = (this.m[2][1] * this.m[1][0]) - (this.m[1][1] * this.m[2][0]);

            // calculate the determinant
            var det = (this.m[0][0] * c01) + (this.m[0][1] * c11) + (this.m[0][2] * c21);
            if (!det) {
                // no solution
                return null;
            }
            var inverseDet = 1 / det;

            var inverseMatrix = MatrixPool.Get();

            inverseMatrix.m[0][0] = c01 * inverseDet;
            inverseMatrix.m[0][1] = ((-this.m[2][2] * this.m[0][1]) + (this.m[0][2] * this.m[2][1])) * inverseDet;
            inverseMatrix.m[0][2] = ((this.m[1][2] * this.m[0][1]) - (this.m[0][2] * this.m[1][1])) * inverseDet;

            inverseMatrix.m[1][0] = c11 * inverseDet;
            inverseMatrix.m[1][1] = ((this.m[2][2] * this.m[0][0]) - (this.m[0][2] * this.m[2][0])) * inverseDet;
            inverseMatrix.m[1][2] = ((-this.m[1][2] * this.m[0][0]) + (this.m[0][2] * this.m[1][0])) * inverseDet;

            inverseMatrix.m[2][0] = c21 * inverseDet;
            inverseMatrix.m[2][1] = ((-this.m[2][1] * this.m[0][0]) + (this.m[0][1] * this.m[2][0])) * inverseDet;
            inverseMatrix.m[2][2] = ((this.m[1][1] * this.m[0][0]) - (this.m[0][1] * this.m[1][0])) * inverseDet;

            return inverseMatrix;
        };

        this.translate = function(x, y) {
            this.m[2][0] += x;
            this.m[2][1] += y;
            return this;
        };
        this.scale = function(x, y) {
            this.m[0][0] *= x;
            this.m[1][1] *= y;
            this.m[1][0] *= x;
            this.m[1][1] *= y;
            this.m[2][0] *= x;
            this.m[2][1] *= y;
            return this;
        };
        this.skew = function(x, y) {
            this.m[0][1] *= y;
            this.m[1][0] *= x;
            return this;
        };
        this.rotate = function(angle) {
            angle = angle * DEG_TO_RAD;
            var c = Math.cos(angle);
            var s = Math.sin(angle);

            var m00 = this.m[0][0];
            var m01 = this.m[0][1];
            var m02 = this.m[0][2];
            var m10 = this.m[1][0];
            var m11 = this.m[1][1];
            var m12 = this.m[1][2];
            var m20 = this.m[2][0];
            var m21 = this.m[2][1];
            var m22 = this.m[2][2];

            this.m[0][0] = (m00 * c) - (m01 * s);
            this.m[0][1] = (m00 * s) + (m01 * c);
            this.m[1][0] = (m10 * c) - (m11 * s);
            this.m[1][1] = (m10 * s) + (m11 * c);
            this.m[2][0] = (m20 * c) - (m21 * s);
            this.m[2][1] = (m20 * s) + (m21 * c);

            return this;
        };

        this.multiply = function(matrix) {
            // adjust current matrix
            var m00 = this.m[0][0];
            var m01 = this.m[0][1];
            var m02 = this.m[0][2];
            var m10 = this.m[1][0];
            var m11 = this.m[1][1];
            var m12 = this.m[1][2];
            var m20 = this.m[2][0];
            var m21 = this.m[2][1];
            var m22 = this.m[2][2];

            var b00 = matrix.m[0][0];
            var b01 = matrix.m[0][1];
            var b10 = matrix.m[1][0];
            var b11 = matrix.m[1][1];

            this.m[0][0] = (m00 * b00) + (m01 * b10);
            this.m[0][1] = (m00 * b01) + (m01 * b11);
            this.m[0][2] = 0;
            this.m[1][0] = (m10 * b00) + (m11 * b10);
            this.m[1][1] = (m10 * b01) + (m11 * b11);
            this.m[1][2] = 0;
            this.m[2][0] = (m20 * b00) + (m21 * b10) + matrix.m[2][0];
            this.m[2][1] = (m20 * b01) + (m21 * b11) + matrix.m[2][1];
            this.m[2][2] = 1;

            return this;
        };

        this.clone = function() {
            var m = MatrixPool.Get();
            m.m[0][0] = this.m[0][0];
            m.m[0][1] = this.m[0][1];
            m.m[0][2] = this.m[0][2];
            m.m[1][0] = this.m[1][0];
            m.m[1][1] = this.m[1][1];
            m.m[1][2] = this.m[1][2];
            m.m[2][0] = this.m[2][0];
            m.m[2][1] = this.m[2][1];
            m.m[2][2] = this.m[2][2];
            return m;
        };

        this.transformPoint = function(x, y) {
            var obj = this;
            return new function() {
                this.x = (x * obj.m[0][0]) + (y * obj.m[0][1]) + obj.m[2][0];
                this.y = (x * obj.m[1][0]) + (y * obj.m[1][1]) + obj.m[2][1];
            };
        };

        this.cssTransform = function() {
            var thisMat = this.m;
            return 'matrix(' + thisMat[0][0].toFixed(7) + ', ' + thisMat[1][0].toFixed(7) + ', ' + thisMat[0][1].toFixed(7) + ', ' + thisMat[1][1].toFixed(7) + ', ' + thisMat[2][0].toFixed(7) + ', ' + -thisMat[2][1].toFixed(7) + ')';
        };
    };

    Matrix.Translate = function(x, y) {
        return (MatrixPool.Get()).translate(x, y);
    };
    Matrix.Scale = function(x, y) {
        return (MatrixPool.Get()).scale(x, y);
    };
    Matrix.Skew = function(x, y) {
        return (MatrixPool.Get()).skew(x, y);
    };
    Matrix.Rotate = function(angle) {
        return (MatrixPool.Get()).rotate(angle);
    };

    var Point = function(x, y) {
        this.x = 0;
        this.y = 0;

        if (x instanceof Point) {
            // hmm... set this object to be the value from the 'x' parameter as it is a Point object
            // should it clone Point object prior if this is not its intention, or pass as "new Point(obj.x, obj.y)"
            return x;
        }
        else if (x instanceof Array && x.length == 2) {
            this.x = parseFloat(x[0]);
            this.y = parseFloat(x[1]);
        }
        else if (x !== undefined && y === undefined) {
            // set both to x
            this.x = x;
            this.y = x;
        }
        else if (x !== undefined && y !== undefined) {
            this.x = x;
            this.y = y;
        }

        this.interpolate = function(name, other, ratio) {
            if (ratio == undefined) {
                ratio = other;
                other = name;
                name = 'point';
            }

            return Interpolation.Method(name, ratio, this, other);
        };
    };

    var Transform = function(x, y, angle, scale) {
        this.x = x;
        this.y = y;
        this.angle = angle;
        this.scale = scale;

        this.endFrameAngle = this.angle;

        this.calculateLocalMatrix = function() {
            var angle = (this.endFrameAngle != undefined ? this.endFrameAngle : (this.angle ? this.angle : 0));

            var localMatrix = MatrixPool.Get();
            MatrixPool.Mark();
            localMatrix.multiply(Matrix.Scale(this.scale ? this.scale : 1, this.scale ? this.scale : 1));
            localMatrix.multiply(Matrix.Rotate(angle));
            localMatrix.multiply(Matrix.Translate(this.x ? this.x : 0, this.y ? this.y : 0));
            MatrixPool.Release();
            return localMatrix;
        };

        this.calculateBoneMatrix = function(boneLength) {
            var angle = (this.endFrameAngle != undefined ? this.endFrameAngle : (this.angle ? this.angle : 0));

            var boneMatrix = MatrixPool.Get();
            MatrixPool.Mark();
            boneMatrix.multiply(Matrix.Translate(boneLength, 0));
            boneMatrix.multiply(Matrix.Rotate(angle));
            boneMatrix.multiply(Matrix.Scale(this.scale ? this.scale : 1, this.scale ? this.scale : 1));
            boneMatrix.multiply(Matrix.Translate(this.x ? this.x : 0, this.y ? this.y : 0));
            MatrixPool.Release();
            return boneMatrix;
        };

        this.interpolate = function(name, other, ratio) {
            if (ratio == undefined) {
                ratio = other;
                other = name;
                name = 'transform';
            }

            var angle = (this.endFrameAngle != undefined ? this.endFrameAngle : (this.angle ? this.angle : 0));

            return new Transform(Interpolation.Method(name, ratio, this.x ? this.x : 0, other.x ? other.x : 0),
                                 Interpolation.Method(name, ratio, this.y ? this.y : 0, other.y ? other.y : 0),
                                 Interpolation.Method(name, ratio, angle, other.angle ? other.angle : 0),
                                 Interpolation.Method(name, ratio, this.scale ? this.scale : 1, other.scale ? other.scale : 1));
        };
    };

    var FrameAction = function(id, animationFrame, name, type, data) {
        this.id = id;
        this.animationFrame = animationFrame;

        this.name = name;
        this.type = type;

        this.data = data;

        this.wasRun = false;

        this.performAction = function(bone, deltaTime, parentMatrix) {
            // ensure this is only called once
            if (!this.wasRun) {
                this.wasRun = true;

                switch (this.type) {
                    case 'function':
                        this.data(bone, deltaTime, parentMatrix);
                        break;
                    case 'addContent':
                        // Content takes: name, type, content, pivot, offset, transform
                        bone.addContent(this.data);
                        break;
                    case 'removeContent':
                        bone.removeContent(this.name);
                        break;
                    case 'grab':
                        bone.grab(this.name, this.data);
                        break;
                    case 'release':
                        bone.release(this.name);
                        break;
                }
            }
        };
    };

    var AnimationFrame = function(frame, boneName, transform, frameActionList) {
        this.frame = frame;
        this.boneName = boneName;
        this.transform = transform;

        this.frameActionList = (frameActionList ? frameActionList : []);

        this.performAction = function(frameActionId, bone, deltaTime, parentMatrix) {
            each(this.frameActionList, function(item) {
                if (item != null && !item.wasRun && item.id == frameActionId) {
                    item.performAction(bone, deltaTime, parentMatrix);
                }
            });
        };

        this.grab = function(name, params) {
            this.frameActionList[this.frameActionList.length] = new FrameAction(this.frameActionList.length, this, name, 'grab', params);
        };

        this.release = function(name) {
            this.frameActionList[this.frameActionList.length] = new FrameAction(this.frameActionList.length, this, name, 'release');
        };

        this.addReset = function() {
            this.frameActionList[this.frameActionList.length] = new FrameAction(this.frameActionList.length, this, null, 'reset');
        };

        this.addFunction = function(name, theFunction) {
            this.frameActionList[this.frameActionList.length] = new FrameAction(this.frameActionList.length, this, name, 'function', theFunction);
        };

        this.addContent = function(options) {
            this.frameActionList[this.frameActionList.length] = new FrameAction(this.frameActionList.length, this, name, 'addContent', options);
        };

        this.removeContent = function(name) {
            this.frameActionList[this.frameActionList.length] = new FrameAction(this.frameActionList.length, this, name, 'removeContent');
        };

        this.update = function(deltaTime, parentMatrix) {
            if (this.boneName) {
                var bone = jBone.findBone(this.boneName);
                each(this.frameActionList, function(item) {
                    if (item != null) {
                        // call up to the original animationFrame object
                        item.animationFrame.performAction(item.id, bone, deltaTime, parentMatrix);
                    }
                });
            } else {
                each(this.frameActionList, function(item) {
                    if (item != null) {
                        // call up to the original animationFrame object
                        item.animationFrame.performAction(item.id, null, deltaTime, parentMatrix);
                    }
                });
            }
        };

        this.interpolate = function(name, other, ratio) {
            if (ratio == undefined) {
                ratio = other;
                other = name;
                name = 'animation';
            }

            return new AnimationFrame(Interpolation.Method(name, ratio, this.frame, other.frame),
                                      this.boneName,
                                      this.transform.interpolate(name, other.transform, ratio),
                                      this.frameActionList);
        };
    };

    var AnimationSet = function(options) {
        // options: name, frameCount, duration, looped
        var defaultParams = {
            name: undefined,
            frames: 1,
            duration: 1000,
            looped: false
        };
        applyDefaults(options, defaultParams);

        this.name = options['name'];
        this.frameCount = options['frames'];
        this.duration = options['duration'];

        this.looped = options['looped'];

        this.animationFrameList = [];

        this.currentSelectedFrame = 0;

        this.currentFrame = 0;
        this.currentInterpolate = 0;

        this.stopped = false;

        this.elapsedTime = 0;
        this.frameElapsedTime = 0;
        this.frameStep = this.duration / (this.looped ? this.frameCount - 1 : this.frameCount);

        this.update = function(deltaTime) {
            if (!this.stopped) {
                this.elapsedTime += deltaTime;
                this.frameElapsedTime += deltaTime;

                if (this.elapsedTime >= this.duration) {
                    if (this.looped) {
                        this.elapsedTime -= this.duration;
                    } else {
                        this.elapsedTime = this.duration;
                        this.stopped = true;
                    }
                }

                if (this.frameElapsedTime >= this.frameStep) {
                    this.frameElapsedTime -= this.frameStep;
                }

                this.currentFrame = parseInt(this.elapsedTime / this.frameStep);
                this.currentInterpolate = this.frameElapsedTime / this.frameStep;
            }
        };

        this.at = function(frame) {
            this.currentSelectedFrame = frame;
            return this;
        };

        this.repeat = function(frameStart, frameEnd) {
            // need to iterate through all the frames from (inclusive) frameStart and frameEnd
            // for each frame
            //    need to copy the data and put it at frameEnd + frameIndex
            //
            return this;
        };

        this.reset = function() {
            // needs to trigger a reset of all held objects (back to their original state)
            var existingFrame = this.findCurrentKeyframeForBoneName(null);
            if (existingFrame) {
                existingFrame.addReset();
            } else {
                var transform = new Transform();
                var frame = new AnimationFrame(this.currentSelectedFrame, null, transform);
                frame.addReset();
                this.animationFrameList[this.animationFrameList.length] = frame;
            }

            return this;
        };

        this.addFunction = function(boneName, name, theFunction) {
            var existingFrame = this.findCurrentKeyframeForBoneName(boneName);
            if (existingFrame) {
                existingFrame.addFunction(name, theFunction);
            } else {
                var transform = new Transform();
                var frame = new AnimationFrame(this.currentSelectedFrame, boneName, transform);
                frame.addFunction(name, theFunction);
                this.animationFrameList[this.animationFrameList.length] = frame;
            }
            return this;
        };

        this.grab = function(boneName, name, params) {
            var existingFrame = this.findCurrentKeyframeForBoneName(boneName);
            if (existingFrame) {
                existingFrame.grab(name, params);
            } else {
                var transform = new Transform();
                var frame = new AnimationFrame(this.currentSelectedFrame, boneName, transform);
                frame.grab(name, params);
                this.animationFrameList[this.animationFrameList.length] = frame;
            }
            return this;
        };

        this.release = function(boneName, name) {
            var existingFrame = this.findCurrentKeyframeForBoneName(boneName);
            if (existingFrame) {
                existingFrame.release(name);
            } else {
                var transform = new Transform();
                var frame = new AnimationFrame(this.currentSelectedFrame, boneName, transform);
                frame.release(name);
                this.animationFrameList[this.animationFrameList.length] = frame;
            }
            return this;
        };

        this.addContent = function(boneName, name, type, content, pivot, offset, transform) {
            var existingFrame = this.findCurrentKeyframeForBoneName(boneName);
            if (existingFrame) {
                existingFrame.addContent(name, type, content, pivot, offset, transform);
            } else {
                var transform = new Transform();
                var frame = new AnimationFrame(this.currentSelectedFrame, boneName, transform);
                frame.addContent(name, type, content, pivot, offset, transform);
                this.animationFrameList[this.animationFrameList.length] = frame;
            }
            return this;
        };

        this.removeContent = function(boneName, name) {
            var existingFrame = this.findCurrentKeyframeForBoneName(boneName);
            if (existingFrame) {
                existingFrame.removeContent(name);
            } else {
                var transform = new Transform();
                var frame = new AnimationFrame(this.currentSelectedFrame, boneName, transform);
                frame.removeContent(name);
                this.animationFrameList[this.animationFrameList.length] = frame;
            }
            return this;
        };

        this.rotate = function(boneName, angle, endFrameAngle) {
            var existingFrame = this.findCurrentKeyframeForBoneName(boneName);
            if (existingFrame) {
                existingFrame.transform.angle += angle;
                if (endFrameAngle != undefined) {
                    existingFrame.transform.endFrameAngle = endFrameAngle;
                }
            } else {
                var transform = new Transform();
                transform.angle = angle;
                if (endFrameAngle != undefined) {
                    transform.endFrameAngle = endFrameAngle;
                }
                var frame = new AnimationFrame(this.currentSelectedFrame, boneName, transform);
                this.animationFrameList[this.animationFrameList.length] = frame;
            }
            return this;
        };

        this.translate = function(boneName, x, y) {
            var existingFrame = this.findCurrentKeyframeForBoneName(boneName);
            if (existingFrame) {
                existingFrame.transform.x += x;
                existingFrame.transform.y += y;
            } else {
                var transform = new Transform();
                transform.x = x;
                transform.y = y;
                var frame = new AnimationFrame(this.currentSelectedFrame, boneName, transform);
                this.animationFrameList[this.animationFrameList.length] = frame;
            }
            return this;
        };

        this.scale = function(boneName, scale) {
            var existingFrame = this.findCurrentKeyframeForBoneName(boneName);
            if (existingFrame) {
                existingFrame.transform.scale += scale;
            } else {
                var transform = new Transform();
                transform.scale = scale;
                var frame = new AnimationFrame(this.currentSelectedFrame, boneName, transform);
                this.animationFrameList[this.animationFrameList.length] = frame;
            }
            return this;
        };

        this.findCurrentKeyframeForBoneName = function(boneName) {
            var obj = this;
            var frame = each(this.animationFrameList, function(item) {
                if (item.frame == obj.currentSelectedFrame && item.boneName == boneName) {
                    return item;
                }
            });

            return frame;
        };

        this.findFrameForBoneName = function(boneName) {
            var obj = this;
            var frameBefore = null;
            each(this.animationFrameList, function(item) {
                if (item.boneName == boneName) {
                    if (item.frame <= obj.currentFrame && (frameBefore == null || item.frame >= frameBefore.frame)) {
                        frameBefore = item;
                    }
                }
            });
            if (frameBefore) {
                var frameAfter = this.findFrameAfterForBoneName(boneName);
                if (frameAfter) {
                    var ratio = this.currentInterpolate;
                    var frames = frameAfter.frame - frameBefore.frame;
                    if (frames > 1) {
                        var frameRatio = 1 / frames;
                        ratio = ((this.currentFrame - frameBefore.frame) * frameRatio) + (frameRatio * this.currentInterpolate);
                    }
                    return frameBefore.interpolate('animation', frameAfter, ratio);
                }
                return frameBefore;
            }
            return null;
        };

        this.findCurrentAnimationFrameForBoneName = function(boneName) {
            var obj = this;
            var frameBefore = null;
            each(this.animationFrameList, function(item) {
                if (item.boneName == boneName) {
                    if (item.frame <= obj.currentFrame && (frameBefore == null || item.frame >= frameBefore.frame)) {
                        frameBefore = item;
                    }
                }
            });
            return frameBefore;
        };

        this.findFrameAfterForBoneName = function(boneName) {
            var obj = this;
            var frameAfter = null;
            each(this.animationFrameList, function(item) {
                if (item.boneName == boneName) {
                    if (item.frame > obj.currentFrame && (frameAfter == null || item.frame < frameAfter.frame)) {
                        frameAfter = item;
                    }
                }
            });

            return frameAfter;
        };
    };

    // 'armImg', 'image', './images/arm.png', [0, 0], [0, 0], [Transform]
    var Content = function(options) {
        // options: name, type, content, pivot, offset, transform
        var defaultParams = {
            name: undefined,
            type: undefined,
            content: null,
            pivot: new Point(0, 0),
            offset: new Point(0, 0),
            transform: new Transform(0, 0, 0, 1)
        };
        applyDefaults(options, defaultParams);

        this.name = options['name'];
        this.type = options['type'];

        this.content = options['content'];

        this.pivot = options['pivot'];
        this.offset = options['offset'];
        this.localTransform = options['transform'];

        this.cachedObj = null;

        this.resetCache = function() {
            this.cachedObject = null;

            if (this.cachedObject == null) {
                this.cachedObject = document.getElementById(this.name);
            }
        };

        this.update = function(bone, deltaTime, parentMatrix) {
            if (this.cachedObject == null) {
                this.cachedObject = document.getElementById(this.name);

                // attempt to create it
                if (this.cachedObject == null && bone.cachedObject != null) {
                    bone.cachedObject.parentNode.innerHTML += this.render();
                    // go up to the parent node and invalid all the child cachedObjects
                    var rootBone = bone;
                    while (rootBone.parentBone != null) {
                        rootBone = rootBone.parentBone;
                    }
                    rootBone.resetCache();

                    // attempt to fetch it again
                    this.cachedObject = document.getElementById(this.name);
                }

                if (this.cachedObject != null) {
                    this.cachedObject.style[cssTransformOriginStr] = '0 0';
                }
            }

            if (this.cachedObject != null) {
                MatrixPool.Mark();

                // calculate matrix for pivot
                var pivotMatrix = MatrixPool.Get();
                pivotMatrix.translate(-this.pivot.x, this.pivot.y);
                pivotMatrix.rotate(this.localTransform.angle);

                // calculate current matrix
                var localMatrix = this.localTransform.calculateLocalMatrix();

                if (parentMatrix) {
                    localMatrix.multiply(parentMatrix);
                }
                localMatrix.translate(this.offset.x, this.offset.y);

                pivotMatrix.multiply(localMatrix);

                this.cachedObject.style[cssTransformStr] = pivotMatrix.cssTransform();

                MatrixPool.Release();
            }
        };

        this.render = function() {
            var output = '';
            switch (this.type) {
                case 'image':
                    var obj = this;
                    var img = new Image();
                    img.src = this.content;
                    img.onload = function() {
                        //obj.localTransform.y = img.height / 2;
                    };
                    // create the content
                    output = "<img id='" + this.name + "' class='jbone-content' src='" + this.content + "' />";
                    break;
                case 'static':
                    output = this.content;
                    break;
                case 'span':
                    output = "<span id='" + this.name + "' class='jbone-content'>" + this.content + "</span>";
                    break;
                case 'target':
                    output = "<span id='" + this.name + "' class='jbone-content-target'></span>";
                    break;
                case 'dynamic':
                    // no need to do anything here...
                    break;
            }
            return output;
        };
    };

    var HeldObject = function(name) {
        this.name = name;
        this.held = true;

        this.originalObject = null;
        this.originalParentObject = null;

        this.cachedObject = null;
        this.cachedObjectDebug = null;

        this.contentTarget = null;

        this.initialTransform = null;
        this.initialAngle = 0;

        this.params = null;

        this.resetObject = function() {
            // 
        };

        this.update = function(bone, deltaTime, parentMatrix) {
            if (this.held) {
                if (this.cachedObject == null) {
                    // grab the element and ensure positioning has been accounted for
                    this.cachedObject = document.getElementById(this.name);

                    // store the original (to restore later)
                    this.originalParentObject = this.cachedObject.parentElement;
                    this.originalObject = this.cachedObject.cloneNode(true);

                    bone.addContent({ name: this.name + '-target', type: 'target' });
                    this.contentTarget = bone.contentList[bone.contentList.length - 1];

                    var rootBone = bone;
                    while (rootBone.parentBone != null) {
                        rootBone = rootBone.parentBone;
                    }

                    var rootPos = elementPosition(rootBone.cachedObject);
                    var objPos = elementPosition(this.cachedObject);

                    this.contentTarget.update(bone, deltaTime, parentMatrix);

                    var bonePos = parentMatrix.transformPoint(0, 0);
                    var targetPos = rootPos;
                    targetPos.left += bonePos.x;
                    targetPos.top -= bonePos.y;

                    this.cachedObject.style['top'] = '0';
                    this.cachedObject.style['left'] = '0';
                    //this.cachedObject.style['bottom'] = '0';
                    //this.cachedObject.style['right'] = '0';
                    this.cachedObject.style['position'] = 'absolute';
                    this.cachedObject.setAttribute('parentId', this.originalParentObject.id);

                    rootBone.cachedObject.parentNode.appendChild(this.cachedObject);
                    this.cachedObject = document.getElementById(this.name);

                    this.initialTransform = new Transform((objPos.left - targetPos.left), (targetPos.top - objPos.top), 0, 1);
                    this.initialAngle = -bone.currentAngle;
                }

                if (this.cachedObject != null) {
                    // calculate current matrix
                    var lockAngle = (this.params ? (this.params['lock'] == 'angle' ? true : false) : false);

                    MatrixPool.Mark();

                    var localMatrix = this.initialTransform.calculateLocalMatrix();

                    localMatrix.multiply(Matrix.Rotate(this.initialAngle));

                    if (lockAngle) {
                        var finalMatrix = Matrix.Rotate(-(this.initialAngle + bone.currentAngle));
                        localMatrix.multiply(finalMatrix);
                    }

                    if (parentMatrix) {
                        var pMatrix = parentMatrix.clone();
                        localMatrix.multiply(pMatrix);
                    }

                    if (this.cachedObject != null) {
                        this.cachedObject.style[cssTransformStr] = localMatrix.cssTransform();
                        this.cachedObject.style[cssTransformOriginStr] = '0 0';
                    }

                    MatrixPool.Release();
                }
            }
        };

        this.grab = function(params) {
            this.held = true;
            this.params = params;

            this.cachedObject = null;
        };

        this.release = function() {
            this.held = false;

            this.cachedObject = null;
        };
    };

    var Bone = function(options) {
        // options: name, selectorId, x, y, angle, boneLength, boneThickness, parentBone, initialPosX, initialPosY
        var defaultParams = {
            name: undefined,
            selectorId: undefined,
            x: 0,
            y: 0,
            angle: 0,
            length: 0,
            thickness: 1,
            parentBone: null,
            initialPosX: 0,
            initialPosY: 0
        };
        applyDefaults(options, defaultParams);

        this.name = options['name'];
        this.renderElementId = options['selectorId'];

        this.angle = options['angle'];
        this.boneLength = options['length'];
        this.boneThickness = options['thickness'];

        this.localTransform = new Transform(options['x'], options['y'], this.angle, 1);
        this.initialTransform = new Transform(options['initialPosX'], options['initialPosY'], 0, 1);

        this.currentAngle = this.angle;
        this.currentEndPointPos = null;

        this.parentBone = options['parentBone'];
        this.childBoneList = [];

        this.contentList = [];

        this.cachedObject = null;
        this.cachedTracer = null;

        this.heldObjectList = [];

        this.resetCache = function() {
            this.cachedObject = null;
            this.cachedTracer = null;

            if (this.cachedObject == null) {
                this.cachedObject = document.getElementById(this.name);
                this.cachedTracer = document.getElementById(this.name + '-trace');
            }

            each(this.childBoneList, function(item) {
                item.resetCache();
            });

            each(this.contentList, function(item) {
                item.resetCache();
            });
        };

        this.branch = function(dataFunc) {
            if (dataFunc != null) {
                dataFunc(this);
            }
            return this;
        };

        this.addChildBone = function(options) {
            options['parentBone'] = this;
            var bone = new Bone(options);
            this.childBoneList[this.childBoneList.length] = bone;
            return bone;
        };

        this.addContent = function(options) {
            var content = new Content(options);
            this.contentList[this.contentList.length] = content;
            return this;
        };

        this.removeContent = function(name) {
            for (var index = 0, length = this.contentList.length; index < length; ++index) {
                if (this.contentList[index] != null && this.contentList[index].name == name) {
                    this.cachedObject.removeChild(this.contentList[index].cachedObject);

                    delete this.contentList[index];
                    this.contentList[index] = null;
                }
            }
            return this;
        };

        this.grab = function(name, params) {
            // grab hold of some element on the page
            var heldObject = null;
            for (var index = 0, length = this.heldObjectList.length; index < length; ++index) {
                if (this.heldObjectList[index] != null && this.heldObjectList[index].name == name) {
                    // reuse existing
                    heldObject = this.heldObjectList[index];
                    break;
                }
            }

            if (heldObject == null) {
                heldObject = new HeldObject(name);
                this.heldObjectList[this.heldObjectList.length] = heldObject;
            }

            heldObject.grab(params);

            return this;
        };

        this.release = function(name) {
            // release a hold of some element on the page
            for (var index = 0, length = this.heldObjectList.length; index < length; ++index) {
                if (this.heldObjectList[index] != null && this.heldObjectList[index].name == name) {
                    this.heldObjectList[index].release();
                    break;
                }
            }
            return this;
        };

        this.findBone = function(boneName) {
            if (this.name == boneName) {
                return this;
            }

            var bone = null;
            if (this.childBoneList != null) {
                bone = each(this.childBoneList, function(item) {
                    var theBone = item.findBone(boneName);
                    if (theBone) {
                        return theBone;
                    }
                });
            }
            return bone;
        };

        this.update = function(deltaTime, parentMatrix) {
            if (this.cachedObject == null) {
                this.cachedObject = document.getElementById(this.name);
                this.cachedTracer = document.getElementById(this.name + '-trace');
            }

            if (this.cachedObject != null) {
                // calculate current matrix
                var localMatrix = this.localTransform.calculateLocalMatrix();

                // need to keep track of the current angle for grabbing content
                this.currentAngle = this.localTransform.angle;
                // add parent angle
                if (this.parentBone) {
                    this.currentAngle += this.parentBone.currentAngle;
                }

                var animationFrame = jBone.findAnimationForBone(this.name);
                var animMatrix = null;
                if (animationFrame) {
                    this.currentAngle += animationFrame.transform.angle;

                    animMatrix = animationFrame.transform.calculateLocalMatrix();
                    if (animMatrix) {
                        localMatrix.multiply(animMatrix);
                    }
                }

                if (parentMatrix) {
                    localMatrix.multiply(parentMatrix);
                }

                if (this.initialTransform) {
                    localMatrix.multiply(this.initialTransform.calculateLocalMatrix());
                }

                if (animationFrame) {
                    animationFrame.update(deltaTime, localMatrix);
                }

                var boneObj = this;

                each(this.heldObjectList, function(item) {
                    if (item != null) {
                        // update the held objects
                        item.update(boneObj, deltaTime, localMatrix);
                    }
                });

                each(this.contentList, function(item) {
                    if (item != null) {
                        // update the content items
                        item.update(boneObj, deltaTime, localMatrix);
                    }
                });

                // need to offset the 'localMatrix' by the thickness/width of the bone
                var newMat = MatrixPool.Get();
                newMat.translate(-(this.boneThickness + jBone.BorderWidth()), (this.boneThickness + jBone.BorderWidth()));
                localMatrix.multiply(newMat);

                var origin = (this.boneThickness + jBone.BorderWidth()) + 'px ' + (this.boneThickness + jBone.BorderWidth()) + 'px';

                this.cachedObject.style[cssTransformStr] = localMatrix.cssTransform();
                this.cachedObject.style[cssTransformOriginStr] = origin;
                this.cachedObject.style['width'] = this.boneLength + ((this.boneThickness * 2)) + 'px';
                this.cachedObject.style['height'] = (this.boneThickness * 2) + 'px';
                this.cachedObject.style['borderWidth'] = jBone.BorderWidth() + 'px';

                var newMatInv = newMat.inverse();
                localMatrix.multiply(newMatInv);
                MatrixPool.Release(newMatInv);
                MatrixPool.Release(newMat);

                if (this.cachedTracer != null) {
                    newMat = MatrixPool.Get();
                    newMat.translate(-0.5, 0.5);
                    localMatrix.multiply(newMat);

                    this.cachedTracer.style[cssTransformStr] = localMatrix.cssTransform();
                    this.cachedTracer.style[cssTransformOriginStr] = '0 50%';
                    this.cachedTracer.style['width'] = this.boneLength + 'px';
                    this.cachedTracer.style['height'] = '1px';

                    newMatInv = newMat.inverse();
                    localMatrix.multiply(newMatInv);
                    MatrixPool.Release(newMatInv);
                    MatrixPool.Release(newMat);
                }

                var endPointSize = (this.boneThickness * 3) + (jBone.BorderWidth() * 2) + 'px';
                var endPoint = new Transform(-((this.boneThickness * 0.5) + (jBone.BorderWidth() * 2)), ((this.boneThickness * 0.5) + (jBone.BorderWidth() * 2)), 0, 1);
                if (this.cachedObject.lastChild != null && this.cachedObject.lastChild.className != null && this.cachedObject.lastChild.className.indexOf('jbone-endpoint') >= 0) {
                    if (this.childBoneList.length == 0) {
                        var lcBoneMatrix = endPoint.calculateBoneMatrix(this.boneLength);
                        this.cachedObject.lastChild.style[cssTransformStr] = lcBoneMatrix.cssTransform();
                        this.cachedObject.lastChild.style['width'] = endPointSize;
                        this.cachedObject.lastChild.style['height'] = endPointSize;
                        this.cachedObject.lastChild.style['borderWidth'] = jBone.BorderWidth() + 'px';
                        this.cachedObject.lastChild.style['borderRadius'] = (this.boneThickness * 4) + 'px';
                        MatrixPool.Release(lcBoneMatrix);
                    } else {
                        // hide the end point as there are child objects
                        this.cachedObject.lastChild.style['display'] = 'none';
                    }
                }
                if (this.cachedObject.firstChild != null && this.cachedObject.firstChild.className != null && this.cachedObject.firstChild.className.indexOf('jbone-endpoint') >= 0) {
                    var fcBoneMatrix = endPoint.calculateBoneMatrix(0);
                    this.cachedObject.firstChild.style[cssTransformStr] = fcBoneMatrix.cssTransform();
                    this.cachedObject.firstChild.style['width'] = endPointSize;
                    this.cachedObject.firstChild.style['height'] = endPointSize;
                    this.cachedObject.firstChild.style['borderWidth'] = jBone.BorderWidth() + 'px';
                    this.cachedObject.firstChild.style['borderRadius'] = (this.boneThickness * 4) + 'px';
                    MatrixPool.Release(fcBoneMatrix);
                }

                var boneMat = this.localTransform.calculateBoneMatrix(this.boneLength);

                if (animationFrame && animMatrix) {
                    boneMat.multiply(animMatrix);
                }
                if (parentMatrix) {
                    boneMat.multiply(parentMatrix);
                }

                each(this.childBoneList, function(item) {
                    // update the child bones
                    item.update(deltaTime, boneMat);
                });

                MatrixPool.Release(animMatrix);
                MatrixPool.Release(boneMat);
            }
        };

        this.render = function() {
            var output = "<div id='" + this.name + "' class='jbone-bone'><div class='jbone-start-endpoint jbone-endpoint'></div><div class='jbone-end-endpoint jbone-endpoint'></div></div>";
            output += "<div id='" + this.name + "-trace' class='jbone-bone-trace'></div>";

            each(this.contentList, function(item) {
                if (item != null) {
                    // render the content
                    output += item.render();
                }
            });

            each(this.childBoneList, function(item) {
                // render the bone
                output += item.render();
            });

            return output;
        };
    };

    var jBone = (function() {
        // list of root bones in the system
        var _boneList = [];

        // list of all animations in the system
        var _animationList = [];

        // timing
        var _elapsedTime = 0;
        var _frameCounter = 0;
        var _framesPerSecond = 0;
        var _lastTime = 0;
        var _deltaTime = 0;

        // callbacks
        var _updateCallback = null;

        var _timeoutInterval = 50;
        var _thresholdTimeout = _timeoutInterval;

        var _windowFocused = true;

        // styling needed for additional calculations
        var _borderWidth = 2;

        // requestAnim shim layer by Paul Irish
        window.requestAnimFrame = (function() {
            return window.requestAnimationFrame ||
            window.webkitRequestAnimationFrame ||
            window.mozRequestAnimationFrame ||
            window.oRequestAnimationFrame ||
            window.msRequestAnimationFrame ||
            function(/* function */callback, /* DOMElement */element) {
                window.setTimeout(callback, 16.667);
            };
        })();

        if (window.attachEvent) {
            window.attachEvent('focus', function() {
                _windowFocused = true;
            });

            window.attachEvent('blur', function() {
                _windowFocused = false;
            });
        }
        else if (window.addEventListener) {
            window.addEventListener('focus', function() {
                _windowFocused = true;
            });

            window.addEventListener('blur', function() {
                _windowFocused = false;
            });
        }

        if (cssTransformAttr) {
            (function update() {
                requestAnimFrame(arguments.callee);

                if (_windowFocused) {
                    // timer
                    if (_lastTime != 0) {
                        _deltaTime = new Date().getTime() - _lastTime;
                        _elapsedTime += _deltaTime;
                        _frameCounter++;
                        if (_elapsedTime > 1000) {
                            _framesPerSecond = _frameCounter;
                            _elapsedTime = 0;
                            _frameCounter = 0;
                        }
                    }

                    each(_animationList, function(item) {
                        // update the animations
                        item.update(_deltaTime);
                    });

                    _thresholdTimeout -= _deltaTime;

                    if (_thresholdTimeout <= 0) {
                        _thresholdTimeout += _timeoutInterval;

                        each(_boneList, function(item) {
                            // update the bone
                            item.update(_deltaTime);
                        });
                    }

                    if (_updateCallback) {
                        _updateCallback(_deltaTime);
                    }
                }

                _lastTime = new Date().getTime();
            })();
        }

        return {
            Transform: function(x, y, angle, scale) { return new Transform(x, y, angle, scale); },
            Point: function(x, y) { return new Point(x, y); },

            BorderWidth: function(width) {
                if (width) {
                    _borderWidth = width;
                }
                return _borderWidth;
            },

            // event callbacks
            onUpdate: function(updateCallback) {
                _updateCallback = updateCallback;
            },

            addBone: function(options) {
                var bone = new Bone(options);
                _boneList[_boneList.length] = bone;
                return bone;
            },

            addAnimation: function(options) {
                var animation = new AnimationSet(options);
                _animationList[_animationList.length] = animation;
                return animation;
            },

            findBone: function(boneName) {
                var bone = each(_boneList, function(item) {
                    var theBone = item.findBone(boneName);
                    if (theBone) {
                        return theBone;
                    }
                });
                return bone;
            },

            findAnimation: function(animationName) {
                var animation = each(_animationList, function(item) {
                    if (item.name == animationName) {
                        return item;
                    }
                });
                return animation;
            },

            findAnimationForBone: function(boneName) {
                var animationFrame = each(_animationList, function(item) {
                    var frame = item.findFrameForBoneName(boneName);
                    if (frame) {
                        return frame;
                    }
                });

                return animationFrame;
            },

            findCurrentAnimationFrameForBoneName: function(frame, boneName) {
                var animationFrame = each(_animationList, function(item) {
                    var frame = item.findCurrentAnimationFrameForBoneName(boneName);
                    if (frame) {
                        return frame;
                    }
                });

                return animationFrame;
            },

            render: function() {
                if (cssTransformAttr) {
                    each(_boneList, function(item) {
                        if (item.renderElementId != null && item.renderElementId != '') {
                            var element = document.getElementById(item.renderElementId);
                            if (element != null) {
                                // render the bone to the back of the element
                                element.innerHTML += item.render();
                            }
                        }
                    });
                }
            },

            update: function() {
                each(_boneList, function(item) {
                    // update the bone
                    item.update(0);
                });
            }
        };
    })();

    window.jBone = jBone;

})(window);
